import Mathlib.Data.Nat.Defs
import Mathlib.Data.Real.Basic 
import Mathlib.Data.NNReal.Basic

import Mathlib.Data.Finset.Basic
import Mathlib.Data.Set.Basic

import Mathlib.Probability.ProbabilityMassFunction.Basic
--variable (α σ : Type)


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


#check Hist.rec

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

structure MDP (σ α : Type) : Type where
  P  : σ → α → σ → ℝ≥0
  r  : σ → α → σ → ℝ
  s₀ : σ

/-- The set of all histories of length T -/
def histories {σ α : Type} (T : ℕ) := { h : Hist σ α | h.length = T }



/--
Computes the probability of a history
-/
noncomputable def probability {σ α : Type} [DecidableEq σ] (m : MDP σ α) 
                              (π : Hist σ α → α → ℝ≥0) (h : Hist σ α) : ℝ≥0 := 
  match h with
      | Hist.init s => if m.s₀ = s then 1. else 0.
      | Hist.pre hp a s' => 
            match hp with
            | Hist.init s => (m.P s a s') * (π hp a) * (probability m hp)  
            | Hist.pre _ _ s => 


--  termination_by h.length`
--  decreasing_by 
--    sorry
    

noncomputable def  reward {σ α : Type} (m : MDP σ α) (h : Hist σ α) : ℝ :=
  match h.pre with
      | List.nil => 0.
      | List.cons ⟨s₁,a⟩ tail => 
        (m.r s₁  a  h.s) + (reward m (h.eattail))  
  termination_by h.length
  decreasing_by 
    sorry


/--
Computes the value function
-/
def value {σ α : Type} [DecidableEq σ] (m : MDP σ α) (h : Hist σ α) (T : ℕ) : ℝ := sorry


--inductive Hprefix {α σ : Type} (p h: Hist α σ) 

/--
Verifies that the prefix of the history is the same
-/
--def History.prefix {α σ : Type} (pre : Hist α σ)  (h : Hist α σ) : Prop :=
--  match pre.head, h.head with
--  | nil, nil => pre.last = h.last
--  | 
    

 
example {α β γ: Type}  (h : α ⊕ β → γ) : ((α → γ) × (β → γ)) := 
  {fst := fun a => h (Sum.inl a),
   snd := fun b => h (Sum.inr b)}

example {α β γ: Type}  (h : ((α → γ) × (β → γ))) : α ⊕ β → γ 
r    | Sum.inl a => h.fst a
    | Sum.inr b => h.snd b


/--
inductive Hist (α σ : Type) : Type where
  | init (s : σ) : Hist α σ
  | app (head : Hist α σ) (a : α) (s : σ) : Hist α σ
--/
