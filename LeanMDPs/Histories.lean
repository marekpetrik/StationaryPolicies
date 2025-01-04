/-
In this file we define histories and operations that are related to them. 

* Defines an MDP
* Defines a history, which is a sequence of states and actions
* Defines a histories consistent with a partial sequence of states and actions
* A general randomized history-dependent policy
* The reward and probability of the history, which is used to compute the value function
* Value function for a history as the expected reward
-/

import Mathlib.Data.Nat.Defs

import Mathlib.Data.Real.Basic 
import Mathlib.Data.NNReal.Basic

--import Mathlib.Data.Set.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Image
import Mathlib.Logic.Function.Defs -- Injective

import Mathlib.Probability.ProbabilityMassFunction.Basic
--variable (α σ : Type)

import LeanMDPs.Finprob

variable {σ α : Type}
--variable [Inhabited σ] [Inhabited α] -- used to construct policies

open NNReal -- for ℝ≥0 notation
open Finprob

section Definitions

/-- Markov decision process -/
structure MDP (σ α : Type) : Type where
  /-- states , TODO: consider 𝒮 or 𝓢 but causes issues-/
  S : Finset σ
  /-- actions, TODO: consider 𝒜 or 𝓐 but causes issues  -/
  A : Finset α
  /-- transition probability s, a, s' -/
  P : σ → α → Δ S  -- TODO : change to S → A → Δ S
  /-- reward function s, a, s' -/
  r : σ → α → σ → ℝ -- TODO: change to S → A → S → ℝ
  
end Definitions

variable {M : MDP σ α}

section Histories

/-- Represents a history. The state is type σ and action is type α. -/
inductive Hist {σ α : Type} (M : MDP σ α)  : Type where
  | init : σ → Hist M
  | prev : Hist M → α → σ → Hist M

/-- Coerces a state to a history -/
instance : Coe σ (Hist M) where
  coe s := Hist.init s

/-- The length of the history corresponds to the zero-based step of the decision -/
def Hist.length : Hist M → ℕ
  | init _ => 0
  | prev h _ _ => 1 + length h 

/-- Nonempty histories -/
abbrev HistNE {σ α : Type} (m : MDP σ α) : Type := {h : Hist m // h.length ≥ 1}

/-- Returns the last state of the history -/
def Hist.last : Hist M → σ
  | init s => s
  | prev _ _ s => s

/-- Appends the state and action to the history --/
def Hist.append (h : Hist M) (as : α × σ) : Hist M :=
  Hist.prev h as.fst as.snd
  
def tuple2hist : Hist M × α × σ → HistNE M
  | ⟨h, as⟩ => ⟨h.append as, Nat.le.intro rfl⟩
def hist2tuple : HistNE M → Hist M × α × σ
  | ⟨Hist.prev h a s, _ ⟩ => ⟨h, a, s⟩
  
open Function 

lemma linv_hist2tuple_tuple2hist : 
      LeftInverse (hist2tuple (M := M)) tuple2hist := fun _ => rfl
lemma inj_tuple2hist_l1 : Injective (tuple2hist (M:=M)) :=
        LeftInverse.injective linv_hist2tuple_tuple2hist
lemma inj_tuple2hist : Injective ((Subtype.val) ∘ (tuple2hist (M:=M))) := 
    Injective.comp (Subtype.val_injective) inj_tuple2hist_l1

def emb_tuple2hist_l1 : Hist M × α × σ ↪ HistNE M := ⟨tuple2hist, inj_tuple2hist_l1⟩
def emb_tuple2hist : Hist M × α × σ ↪ Hist M  := ⟨λ x ↦ tuple2hist x, inj_tuple2hist⟩

--- state
def state2hist (s : σ) : Hist M := Hist.init s
def hist2state : Hist M → σ | Hist.init s => s | Hist.prev _ _ s => s
    
lemma linv_hist2state_state2hist : LeftInverse (hist2state (M:=M)) state2hist := fun _ => rfl
lemma inj_state2hist : Injective (state2hist (M:=M)) := 
                     LeftInverse.injective linv_hist2state_state2hist
                     
def state2hist_emb : σ ↪ Hist M := ⟨state2hist, inj_state2hist⟩


/-- Checks if pre is the prefix of h. -/
def isprefix : Hist M → Hist M → Prop 
    | Hist.init s₁, Hist.init s₂ => s₁ = s₂
    | Hist.init s₁, Hist.prev hp _ _ => isprefix (Hist.init s₁) hp 
    | Hist.prev _ _ _, Hist.init _ => False
    | Hist.prev h₁ a₁ s₁', Hist.prev  h₂ a₂ s₂' => 
        if h₁.length > h₂.length then
            False
        else if h₁.length < h₂.length then
            let pre := Hist.prev h₁ a₁ s₁' 
            isprefix pre h₂
        else
            (a₁ = a₂) ∧ (s₁' = s₂') ∧ (isprefix h₁ h₂)

/-- All histories of additional length T that follow history h -/
def Histories (h : Hist M) : ℕ → Finset (Hist M) 
    | Nat.zero => {h}
    | Nat.succ t => ((Histories h t) ×ˢ M.A ×ˢ M.S).map emb_tuple2hist

abbrev ℋ : Hist M → ℕ → Finset (Hist M) := Histories

/-- All histories of a given length  -/
def HistoriesHorizon : ℕ → Finset (Hist M)
  | Nat.zero => M.S.map state2hist_emb 
  | Nat.succ t => ((HistoriesHorizon t) ×ˢ M.A ×ˢ M.S).map emb_tuple2hist

abbrev ℋₜ : ℕ → Finset (Hist M) := HistoriesHorizon

--theorem Histories

end Histories

section Policies

/-- Decision rule -/
def DecisionRule (M : MDP σ α) := σ → M.A

abbrev 𝒟 : MDP σ α → Type := DecisionRule

/-- A randomized history-dependent policy -/
def PolicyHR (M : MDP σ α) : Type := Hist M → Δ M.A
abbrev Phr : MDP σ α → Type := PolicyHR

/-- A deterministic Markov policy -/
def PolicyMD (M : MDP σ α) : Type := ℕ → DecisionRule M
abbrev Pmd : MDP σ α → Type := PolicyMD

/-- A deterministic stationary policy -/
def PolicySD (M : MDP σ α) : Type := DecisionRule M
abbrev Psd : MDP σ α → Type := PolicySD

instance [DecidableEq α] : Coe (PolicySD M) (PolicyHR M) where
  coe d := fun h ↦ dirac_dist M.A (d h.last)

instance [DecidableEq α] : Coe (PolicyMD M) (PolicyHR M) where
  coe d := fun h ↦ dirac_dist M.A (d h.length h.last)

end Policies

section Distribution

/-- Probability distribution over histories induced by the policy and 
    transition probabilities -/
def HistDist (h : Hist M) (π : PolicyHR M) (T : ℕ) : Δ (ℋ h T) :=
  match T with 
    | Nat.zero => dirac_ofsingleton h
    | Nat.succ t => 
      let prev := HistDist h π t 
      let update h' (as : α × σ) := ((π h').p as.1 * (M.P h'.last as.1).p as.2)
      let probability : Hist M → ℝ≥0 
        | Hist.init _ => 0 --ignored
        | Hist.prev h' a s => prev.p h' * update h' ⟨a,s⟩
      -- proof of probability
      let sumsto_as (h' : Hist M) _ : ∑ as ∈ M.A ×ˢ M.S, update h' as = 1 :=
          prob_prod_prob (π h').p (fun a =>(M.P h'.last a).p ) 
                         (π h').sumsto (fun a _ => (M.P h'.last a).sumsto)
      let sumsto : ∑ ⟨h',as⟩ ∈ ((ℋ h t) ×ˢ M.A ×ˢ M.S), prev.p h' * update h' as = 1 := 
          prob_prod_prob prev.p update prev.sumsto sumsto_as 
      let HAS := ((ℋ h t) ×ˢ M.A ×ˢ M.S).map emb_tuple2hist
      have sumsto_fin : ∑ h' ∈ HAS, probability h'  = 1 := 
          (Finset.sum_map ((ℋ h t) ×ˢ M.A ×ˢ M.S) emb_tuple2hist probability) ▸ sumsto
      ⟨probability, sumsto_fin⟩

abbrev Δℋ (h : Hist M) (π : PolicyHR M) (T : ℕ) : Finprob (Hist M) := 
          ⟨ℋ h T, HistDist h π T⟩

/- Computes the probability of a history -/
/-def probability  (π : PolicyHR m) : Hist m → ℝ≥0 
      | Hist.init s => m.μ.p s
      | Hist.prev hp a s' => probability π hp * ((π hp).p a * (m.P hp.last a).p s')  
-/

/-- Reward of a history -/
def reward : Hist M → ℝ 
    | Hist.init _ => 0
    | Hist.prev hp a s' => (M.r hp.last a s') + (reward hp)  

/-- The probability of a history -/
def prob_h (h : Hist M) (π : PolicyHR M) (T : ℕ) (h' : ℋ h T) : ℝ≥0 := (Δℋ h π T).2.p h'

/- ----------- Expectations ---------------- -/

--variable {ρ : Type} [HMulZero ρ] [HMul ℕ ρ ρ] [AddCommMonoid ρ]

/-- Expectation over histories for a r.v. X for horizon T and policy π -/
def expect_h (h : Hist M) (π : PolicyHR M) (T : ℕ) (X : Hist M → ℝ) : ℝ := 
        have P := Δℋ h π T
        expect (⟨X⟩ : Finrv P ℝ)

notation "𝔼ₕ[" X "//" h "," π "," t "]" => expect_h h π t X

/-- The k-th state of a history -/
def state [Inhabited σ] (k : ℕ) (h : Hist M) : σ := 
    match h with
    | Hist.init s => if h.length = k then s else Inhabited.default
    | Hist.prev h' _ s => if h.length = k then s else state k h'
    
   
/-- The k-th state of a history -/
def action  [Inhabited α] (k : ℕ) (h : Hist M) : α := 
    match h with
    | Hist.init _ => Inhabited.default
    | Hist.prev h' a _ => if h.length = k then a else action k h'
    

#check List ℕ    

end Distribution

/- Conditional expectation with future singletons -/
/-theorem hist_tower_property {hₖ : Hist m} {π : PolicyHR m} {t : ℕ} {f : Hist m → ℝ}
  (valid : hₖ ∈ ℋ hₖ t) 
  : 𝔼ₕ hₖ π 1 f = (∑ a ∈ m.A, ∑ s ∈ m.S, f (Hist.prev hₖ a s)) := sorry
-/
-- TODO: write a general tower property result first, and then derive a version of this
-- result, which needs to apply over multiple time steps. 

/-
TODO:
2. Show that is the policy is Markov then also the value function is Markov
-/
