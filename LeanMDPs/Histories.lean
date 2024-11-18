import Mathlib.Data.Nat.Defs
import Mathlib.Data.Real.Basic 
import Mathlib.Data.NNReal.Basic

--import Mathlib.Data.Set.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Image
import Mathlib.Logic.Function.Defs -- Injective

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
#check Multiset.sum
#check Set

#eval 1 ∈ [1,2,3] 
#check Membership.mem [1,2,3] 1
 
#check Inhabited
#check Embedding

variable {σ α : Type}
variable [Inhabited σ] [Inhabited α]
variable [DecidableEq σ] [DecidableEq α]

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
def Hist.length : Hist σ α → ℕ
  | init _ => 0
  | prev h _ _ => HAdd.hAdd (length h) 1

/-- returns the last state of the history -/
def Hist.laststate  : Hist σ α → σ
  | init s => s
  | prev _ _ s => s

/-- appends the state and action to the history --/
def Hist.append {σ α : Type} (h : Hist σ α) (as : α × σ) : Hist σ α :=
  Hist.prev h as.fst as.snd
  
/--
Creates new histories from combinations of shorter histories
and states and actions.
-/
def append_hist : Hist σ α × α × σ → Hist σ α 
  | ⟨h, as⟩ => h.append as

def append_hist_linv : Hist σ α → Hist σ α × α × σ
  | Hist.prev h a s => ⟨ h, a, s ⟩
  -- the second case is not used
  | Hist.init _ => ⟨ (Hist.init default), default, default ⟩

/-- Proves that history append has a left inverse. This is used 
    to show that the append_hist is an embedding, useful when 
    constructing a set of histories -/
lemma linv_append_hist {σ α : Type}  [Inhabited σ] [Inhabited α] : 
    Function.LeftInverse (append_hist_linv (σ := σ) (α := α)) append_hist := fun _ => rfl

/--
checks if pre is the prefix of h. This is needed when defining value functions
-/
def isprefix [DecidableEq σ] [DecidableEq α] (pre : Hist σ α) (h : Hist σ α) : Prop :=
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

TODO: Consider defining P and r only of the subtypes constructed from 
the Finsets 𝒮 and 𝒜
-/
structure MDP (σ α : Type) : Type where
  /-- states , TODO: consider \McS but causes issues-/
  SS : Finset σ
  /-- actions, TODO: consider \McA but causes issues  -/
  AA : Finset α
  /-- transition probability s, a, s' -/
  -- TODO: should be a probability distribution
  P  : σ → α → σ → ℝ≥0
  /-- proof of transition probability --/
  prob : (s : σ) → (a : α) → (∑ s' ∈ SS, P s a s') = 1
  /-- reward function s, a, s' -/
  r  : σ → α → σ → ℝ
  /-- initial state -/
  s₀ : σ
  -- TODO: all these functions need to be only defined for states and actions
  -- should be using a Subtype {s // s ∈ states} and Finset attach?

/--
A general randomized history-dependent policy
-/
structure Policy (m : MDP σ α) : Type where
  π : Hist σ α → α → ℝ≥0
  /-- proof that it sums to 1 for all states -/
  prob : (h : Hist σ α) → (∑ a ∈ m.AA, π h a) = 1

/-- The set of all histories of length T -/
def HistAll {σ α : Type} (T : ℕ) := { h : Hist σ α | h.length = T }


-- Need to prove the function used in the construction is injective

 
--lemma append_hist_inj : Function.Injective (append_hist (σ := σ) (α := α)) :=
--   fun a₁ a₂ eq => Eq.rec (fun a b => rfl) eq
     

/--
Creates new histories from combinations of shorter histories
and states and actions.

The embedding guarantees it is injective
-/
def emb_hist_as : Hist σ α × α × σ ↪ Hist σ α :=
 { toFun := append_hist, inj' := Function.LeftInverse.injective linv_append_hist }

/-- 
Set of all policies that follow history pre.
Note that this is just a definition of the set and not a specific instance of the set

The function allhist constructs all histories that satisfy the condition of this set
-/
def PHist  [DecidableEq σ] [DecidableEq α] 
          (m : MDP σ α) (pre : Hist σ α) (T : ℕ) : Finset (Hist σ α)  := 
             if T < pre.length then
               Finset.empty
             else if T = pre.length then
               {pre}
             else
               let AS := Finset.product m.AA  m.SS
               let HAS := Finset.product (PHist m pre (T-1)) AS
               Finset.map emb_hist_as HAS 
               
/--
Computes the probability of a history
-/
noncomputable def probability  [DecidableEq σ] (m : MDP σ α) 
                              (π : Policy m) : Hist σ α → ℝ≥0 
      | Hist.init s => if m.s₀ = s then 1. else 0.
      | Hist.prev hp a s' => (m.P hp.laststate a s') * (π.π hp a) * (probability m π hp)  

/--
Computes the reward of a history
-/
noncomputable def reward  (m : MDP σ α) :  Hist σ α → ℝ 
    | Hist.init _ => 0.
    | Hist.prev hp a s'  =>  (m.r hp.laststate a s') + (reward m hp)  


/-- show that history probabilities are actually a probability distribution -/
lemma probability_dist (m : MDP σ α) (pre : Hist σ α) (π : Policy m) (T : ℕ) : 
                       (∑ h ∈ PHist m pre T, (fun h => probability m π) h) = 1 := sorry


#check Finset.sum


/-

TODO:

1. Dynamic program for histories
2. Show that is the policy is Markov then also the value function is Markov

-/
