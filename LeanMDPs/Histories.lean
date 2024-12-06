import Mathlib.Data.Nat.Defs

import Mathlib.Data.Real.Basic 
import Mathlib.Data.NNReal.Basic

--import Mathlib.Data.Set.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Image
import Mathlib.Logic.Function.Defs -- Injective

import Mathlib.Probability.ProbabilityMassFunction.Basic
--variable (α σ : Type)

import LeanMDPs.FinPr

/-
In this file we define histories and operations that are related to them. 

* Defines an MDP
* Defines a history, which is a sequence of states and actions
* Defines a histories consistent with a partial sequence of states and actions
* A general randomized history-dependent policy
* The reward and probability of the history, which is used to compute the value function
* Value function for a history as the expected reward
-/

variable {σ α : Type}
variable [Inhabited σ] [Inhabited α] -- used to construct policies

open NNReal -- for ℝ≥0 notation
open FinP

/--
The Markov decision process definition 

TODO: Consider defining P and r only of the subtypes constructed from 
the Finsets S and A
-/
structure MDP (σ α : Type) : Type where
  /-- states , TODO: consider 𝒮 or 𝓢 but causes issues-/
  S : Finset σ
  /-- actions, TODO: consider 𝒜 or 𝓐 but causes issues  -/
  A : Finset α
  /-- transition probability s, a, s' -/
  P : σ → α → Δ S  -- TODO : change to S → A → Δ S
  /-- reward function s, a, s' -/
  r : σ → α → σ → ℝ -- TODO: change to S → A → S → ℝ
  /-- initial distribution -/
  μ : Δ S

variable {m : MDP σ α}

/--
Represents a history. The state is type σ and action is type α.

The representation of the history is backwards to facilitate the 
application of a policy
-/
inductive Hist {σ α : Type} (m : MDP σ α)  : Type where
  | init : σ → Hist m
  | prev : Hist m → α → σ → Hist m

/--
The length of the history corresponds to the zero-based step of the decision
-/
def Hist.length : Hist m → ℕ
  | init _ => 0
  | prev h _ _ => HAdd.hAdd (length h) 1

/-- returns the last state of the history -/
def Hist.last  : Hist m → σ
  | init s => s
  | prev _ _ s => s

/-- appends the state and action to the history --/
def Hist.append (h : Hist m) (as : α × σ) : Hist m :=
  Hist.prev h as.fst as.snd
  
/--
Creates new histories from combinations of shorter histories
and states and actions.
-/
def tuple2hist : Hist m × α × σ → Hist m
  | ⟨h, as⟩ => h.append as

def hist2tuple : Hist m → Hist m × α × σ
  | Hist.prev h a s => ⟨ h, a, s ⟩
  -- the second case is not used
  | Hist.init s => ⟨ (Hist.init s), default, default ⟩

/-- Proves that history append has a left inverse. This is used 
    to show that the tupple2hist is an embedding, useful when 
    constructing a set of histories -/
lemma linv_hist2tuple_tuple2hist : 
         Function.LeftInverse (hist2tuple (m := m) ) tuple2hist := fun _ => rfl

/--
Creates new histories from combinations of shorter histories
and states and actions. The embedding guarantees it is injective
-/
def emb_tuple2hist : Hist m × α × σ ↪ Hist m :=
 { toFun := tuple2hist, inj' := Function.LeftInverse.injective linv_hist2tuple_tuple2hist }

/-- Checks if pre is the prefix of h. -/
def isprefix : Hist m →  Hist m → Prop 
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

/-- A randomized history-dependent policy -/
def PolicyHR (m : MDP σ α) := Hist m → Δ m.A

/-- 
Set of all histories of additional length T that follow history `h`.
-/
def Histories (h : Hist m) : ℕ → Finset (Hist m) 
    | Nat.zero => {h}
    | Nat.succ t =>  ((Histories h t) ×ˢ m.A ×ˢ m.S).map emb_tuple2hist 

abbrev ℋ : Hist m → ℕ → Finset (Hist m) := Histories


def HistDist (hₖ : Hist m) (π : PolicyHR m) (T : ℕ) : Δ (ℋ hₖ T) :=
  match T with 
    | Nat.zero => dirac_ofsingleton hₖ
    | Nat.succ t => 
      let prev := HistDist hₖ π t -- previous history
      -- probability of the history
      let f h (as : α × σ) := ((π h).p as.1 * (m.P h.last as.1).p as.2)
      -- the second parameter below is the proof of being in Phist pre t; not used
      let sumsto_as (h' : Hist m) _ : ∑ as ∈ m.A ×ˢ m.S, f h' as = 1 :=
          prob_prod_prob (π h').p (fun a =>(m.P h'.last a).p ) 
                         (π h').sumsto (fun a _ => (m.P h'.last a).sumsto)
      let sumsto : ∑ ⟨h,as⟩ ∈ ((Histories hₖ t) ×ˢ m.A ×ˢ m.S), prev.p h * f h as = 1 := 
          prob_prod_prob prev.p f prev.sumsto sumsto_as 
      let HAS := ((Histories hₖ t) ×ˢ m.A ×ˢ m.S).map emb_tuple2hist
      let p : Hist m → ℝ≥0 
        | Hist.init _ => 0
        | Hist.prev h' a s => prev.p h' * f h' ⟨a,s⟩
      let sumsto_fin : ∑ h ∈ HAS, p h  = 1 := 
          (Finset.sum_map ((Histories hₖ t) ×ˢ m.A ×ˢ m.S) emb_tuple2hist p) ▸ sumsto
      {p := p, sumsto := sumsto_fin}

abbrev Δℋ : (h : Hist m) → PolicyHR m → (T : ℕ) → Δ (ℋ h T) := HistDist

/-- Computes the probability of a history -/
def probability (π : PolicyHR m) : Hist m → ℝ≥0 
      | Hist.init s => m.μ.p s
      | Hist.prev hp a s' => probability π hp * ((π hp).p a * (m.P hp.last a).p s')  
 
def probability_pre  (π : PolicyHR m) : Hist m → ℝ≥0 
      | Hist.init s => m.μ.p s
      | Hist.prev hp a s' => probability π hp * ((π hp).p a * (m.P hp.last a).p s')  

/-- Compute the probability of a history 
-/
def ℙₕ (pre : Hist m) (π : PolicyHR m) (T : ℕ)  : FinP (Histories pre T) := sorry

/--
Computes the reward of a history
-/
def reward : Hist m → ℝ 
    | Hist.init _ => 0.
    | Hist.prev hp a s' => (m.r hp.last a s') + (reward hp)  



/-
TODO:
2. Show that is the policy is Markov then also the value function is Markov
-/
