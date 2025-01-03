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

variable {M : MDP σ α}

/-- Represents a history. The state is type σ and action is type α. -/
inductive Hist {σ α : Type} (M : MDP σ α)  : Type where
  | init : σ → Hist M
  | prev : Hist M → α → σ → Hist M

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

/-- Proves that history append has a left inverse. -/
lemma linv_hist2tuple_tuple2hist : 
      Function.LeftInverse (hist2tuple (M := M)) tuple2hist := fun _ => rfl

lemma inj_tuple2hist_l1 : Function.Injective (tuple2hist (M:=M)) :=
            Function.LeftInverse.injective linv_hist2tuple_tuple2hist

lemma inj_tuple2hist :  
  Function.Injective ((Subtype.val) ∘ (tuple2hist (M:=M))) := 
    Function.Injective.comp (Subtype.val_injective) inj_tuple2hist_l1

/-- New history from a tuple. -/
def emb_tuple2hist_l1 : Hist M × α × σ ↪ HistNE M :=
 { toFun := tuple2hist, inj' := inj_tuple2hist_l1 }
 
def emb_tuple2hist : Hist M × α × σ ↪ Hist M  :=
 { toFun := fun x => tuple2hist x, inj' := inj_tuple2hist }

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

/-- Decision rule -/
def DecisionRule (M : MDP σ α) := σ → M.A

/-- A randomized history-dependent policy -/
def PolicyHR (M : MDP σ α) : Type := Hist M → Δ M.A
abbrev Phr : MDP σ α → Type := PolicyHR

/-- A deterministic Markov policy -/
def PolicyMD (M : MDP σ α) : Type := ℕ → σ → M.A 
abbrev Pmd : MDP σ α → Type := PolicyMD

/-- A deterministic stationary policy -/
def PolicySD (M : MDP σ α) : Type := σ → M.A
abbrev Psd : MDP σ α → Type := PolicySD

instance [DecidableEq α] : Coe (PolicySD M) (PolicyHR M) where
  coe d := fun h ↦ dirac_dist M.A (d h.last)

instance [DecidableEq α] : Coe (PolicyMD M) (PolicyHR M) where
  coe d := fun h ↦ dirac_dist M.A (d h.length h.last)

/-- Set of all histories of additional length T that follow history `h`. -/
def Histories (h : Hist M) : ℕ → Finset (Hist M) 
    | Nat.zero => {h}
    | Nat.succ t => ((Histories h t) ×ˢ M.A ×ˢ M.S).map emb_tuple2hist

abbrev ℋ : Hist M → ℕ → Finset (Hist M) := Histories

/-- Probability distribution over histories induced by the policy and 
    transition probabilities -/
def HistDist (h : Hist M) (π : PolicyHR M) (T : ℕ) : Δ (ℋ h T) :=
  match T with 
    | Nat.zero => dirac_ofsingleton h
    | Nat.succ t => 
      let prev := HistDist h π t -- previous history
      -- probability of the history
      let f h' (as : α × σ) := ((π h').p as.1 * (M.P h'.last as.1).p as.2)
      -- the second parameter below is the proof of being in Phist pre t; not used
      let sumsto_as (h' : Hist M) _ : ∑ as ∈ M.A ×ˢ M.S, f h' as = 1 :=
          prob_prod_prob (π h').p (fun a =>(M.P h'.last a).p ) 
                         (π h').sumsto (fun a _ => (M.P h'.last a).sumsto)
      let sumsto : ∑ ⟨h',as⟩ ∈ ((Histories h t) ×ˢ M.A ×ˢ M.S), prev.p h' * f h' as = 1 := 
          prob_prod_prob prev.p f prev.sumsto sumsto_as 
      let HAS := ((Histories h t) ×ˢ M.A ×ˢ M.S).map emb_tuple2hist
      let p : Hist M → ℝ≥0 
        | Hist.init _ => 0 --ignored
        | Hist.prev h' a s => prev.p h' * f h' ⟨a,s⟩
      have sumsto_fin : ∑ h' ∈ HAS, p h'  = 1 := 
          (Finset.sum_map ((Histories h t) ×ˢ M.A ×ˢ M.S) emb_tuple2hist p) ▸ sumsto
      ⟨p, sumsto_fin⟩

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

--theorem hdist_eq_prod_pi_P  (h : Hist M) (π : Π) 

/- ----------- Expectations ---------------- -/


--variable {ρ : Type} [HMulZero ρ] [HMul ℕ ρ ρ] [AddCommMonoid ρ]

/-- Expectation over histories for a r.v. X for horizon T and policy π -/
def expect_h (h : Hist M) (π : PolicyHR M) (T : ℕ) (X : Hist M → ℝ) : ℝ := 
        have P := Δℋ h π T
        expect (⟨X⟩ : Finrv P ℝ)

notation "𝔼ₕ[" X "//" h "," π "," T "]" => expect_h h π T X

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
