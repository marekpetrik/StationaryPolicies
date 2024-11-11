import Mathlib.Data.Nat.Defs
import Mathlib.Data.Real.Basic 
import Mathlib.Data.NNReal.Basic

import Mathlib.Data.Finset.Basic
import Mathlib.Data.Set.Basic

import Mathlib.Probability.ProbabilityMassFunction.Basic
--variable (α σ : Type)


/-
In this file we define histories and operations that are related to them. 

* Defines an MDP
* Defines a history, which is a sequence of states and actions
* Defines a histories consistent with a partial sequence of states and actions
* A general randomized history-dependent policy
* The reward and probability of the history, which is used to compute the value function
* Value function for a history as the expected reward

-/

#check PMF
#check Finset
#check Sigma 
#check Set

/--
Represents a history. The state is type σ and action is type α.

The representation of the history is backwards to facilitate the 
application of a policy
-/
inductive Hist (σ α : Type)  : Type where
  | init : σ → Hist σ α
  | prev : Hist σ α → α → σ → Hist σ α  

/--
The length of the history corresponds to the zero-based step of the decision
-/
def Hist.length {σ α : Type} : Hist σ α → ℕ
  | init _ => 0
  | prev h _ _ => HAdd.hAdd (length h) 1

/-- returns the last state of the history -/
def Hist.laststate {σ α : Type} : Hist σ α → σ
  | init s => s
  | prev _ _ s => s


--  Hist.rec (fun _ => 0) (fun hp _ _ _ => 1 + hp.length) h

/--
checks if pre is the prefix of h
-/
def isprefix {σ α : Type} [DecidableEq σ] [DecidableEq α] (pre : Hist σ α) (h : Hist σ α) : Prop :=
  match pre, h with
    | Hist.init s₁, Hist.init s₂ => s₁ = s₂
    | Hist.init _, Hist.prev hp _ _ => isprefix pre hp 
    | Hist.prev _ _ _, Hist.init _ => False
    | Hist.prev h₁ a₁ s₁', Hist.prev  h₂ a₂ s₂' => 
        if h₁.length > h₂.length then
            False
        else if h₁.length < h₂.length then
            isprefix pre h₂
        else
            (a₁ = a₂) ∧ (s₁' = s₂') ∧ (isprefix h₁ h₂)

open NNReal -- for ℝ≥0 notation

/--
The Markov decision process definition 
-/
structure MDP (σ α : Type) : Type where
  states : Finset σ
  actions : Finset α
  P  : σ → α → σ → ℝ≥0
  r  : σ → α → σ → ℝ
  s₀ : σ

/--
A general randomized history-dependent policy
-/
structure Policy {σ α : Type} (m : MDP σ α) : Type where
  π : Hist σ α → α → ℝ≥0
  /-- proof that it sums to 1 for all states -/
  sproof : (h : Hist σ α) → (∑ a ∈ m.actions, π h a) = 1

/-- The set of all histories of length T -/
def HistAll {σ α : Type} (T : ℕ) := { h : Hist σ α | h.length = T }

/-- 
Set of all policies that follow history pre.
Note that this is just a definition of the set and not a specific instance of the set

The function allhist constructs all histories that satisfy the condition of this set
-/
def PHist {σ α : Type} [DecidableEq σ] [DecidableEq α] 
          (pre : Hist σ α) (T : ℕ) := Finset {h : Hist σ α | (isprefix pre h) ∧ h.length = T} 

/-- Constructs all histories that satisfy the condition -/
def all_hist {σ α : Type} [DecidableEq σ] [DecidableEq α] 
          (pre : Hist σ α) (T : ℕ)  : PHist pre T := sorry

/--
Computes the probability of a history
-/
noncomputable def probability {σ α : Type} [DecidableEq σ] (m : MDP σ α) 
                              (π : Policy m) : Hist σ α → ℝ≥0 
      | Hist.init s => if m.s₀ = s then 1. else 0.
      | Hist.prev hp a s' => (m.P hp.laststate a s') * (π.π hp a) * (probability m π hp)  

/--
Computes the reward of a history
-/
noncomputable def  reward {σ α : Type} (m : MDP σ α) :  Hist σ α → ℝ 
    | Hist.init _ => 0.
    | Hist.prev hp a s'  =>  (m.r hp.laststate a s') + (reward m hp)  


/-- show that history probabilities are actually a probability distribution -/
lemma probability_dist {σ α : Type} [DecidableEq σ] [DecidableEq α] 
                       (m : MDP σ α) (pre : Hist σ α) (π : Policy m) (T : ℕ) : 
                       (∑ h ∈ all_hist pre T, (fun h => probability m π) h) = 1 := sorry


/--
Defines the value function for a fixed history-dependent policy
-/
noncomputable 
def value {σ α : Type} [DecidableEq σ] [DecidableEq α](m : MDP σ α) 
                  (π : Policy m) (pre : Hist σ α) (T : ℕ) : ℝ := 
    let ha := all_hist pre T
    ∑ (h ∈ ha), (fun h => (probability m π h) * (reward m h)) h
    -- the charater above is NOT Σ but is ∑ typed as \sum
