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


variable {σ α : Type}
variable [Inhabited σ] [Inhabited α]

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
  P : σ → α → σ → ℝ≥0
  /-- proof of transition probability --/
  prob : (s : σ) → (a : α) → (∑ s' ∈ SS, P s a s') = 1
  /-- reward function s, a, s' -/
  r : σ → α → σ → ℝ
  /-- initial state -/
  s₀ : σ
  s₀inSS : (s₀ ∈ SS)
  -- TODO: all these functions need to be only defined for states and actions
  -- should be using a Subtype {s // s ∈ states} and Finset attach?

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
def Hist.laststate  : Hist m → σ
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
  | Hist.init _ => ⟨ (Hist.init default), default, default ⟩

/-- Proves that history append has a left inverse. This is used 
    to show that the tupple2hist is an embedding, useful when 
    constructing a set of histories -/
lemma linv_append_hist : Function.LeftInverse (hist2tuple (m := m) ) tuple2hist := fun _ => rfl

/--
Checks if pre is the prefix of h. This is needed when defining value functions
-/
def isprefix (pre : Hist m) (h : Hist m) : Prop :=
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

/--
A general randomized history-dependent policy
-/
structure Policy (m : MDP σ α) : Type where
  π : Hist m → α → ℝ≥0
  /-- proof that it sums to 1 for all states -/
  prob : (h : Hist m) → (∑ a ∈ m.AA, π h a) = 1

/--
Creates new histories from combinations of shorter histories
and states and actions.

The embedding guarantees it is injective
-/
def emb_tuple2hist : Hist m × α × σ ↪ Hist m :=
 { toFun := tuple2hist, inj' := Function.LeftInverse.injective linv_append_hist }

/-- 
Set of all policies that follow history pre.
Note that this is just a definition of the set and not a specific instance of the set

T is the number of steps beyond the history pre
-/
def PHist (pre : Hist m) (T : ℕ) : Finset (Hist m) := 
    match T with 
      | Nat.zero => {pre}
      | Nat.succ t => Finset.map emb_tuple2hist ((PHist pre t) ×ˢ m.AA ×ˢ m.SS)

/--
Computes the probability of a history
-/
noncomputable def probability [DecidableEq σ] (π : Policy m) : Hist m → ℝ≥0 
      | Hist.init s => if m.s₀ = s then 1. else 0.
      | Hist.prev hp a s' => probability π hp * (π.π hp a * m.P hp.laststate a s')  
 
noncomputable def probability_has [DecidableEq σ] (π : Policy m) : Hist m × α × σ → ℝ≥0 
      | ⟨h,a,s⟩ => probability π h * (π.π h a * m.P h.laststate a s)

lemma hist_prob (π : Policy m) [DecidableEq σ]: 
        ∀ has, probability π (emb_tuple2hist has) = probability_has π has := fun _ => rfl
/--
Computes the reward of a history
-/
noncomputable def reward : Hist m → ℝ 
    | Hist.init _ => 0.
    | Hist.prev hp a s' => (m.r hp.laststate a s') + (reward hp)  

--example {S₁ S₂ : Finset σ} (s₁ : σ) (f : ℝ ) (g : σ → ℝ) : f*(∑ s₂ ∈ S₂, (g s₂)) = ∑ s₂ ∈ S₂, f*(g s₂) := by apply Finset.mul_sum

lemma prob_prod {A : Finset α} {S : Finset σ} (f : α → ℝ) (g : σ → ℝ) 
                 (h1 : ∑ s ∈ S, g s = 1) (h2 : ∑ a ∈ A, f a = 1): 
          (∑ sa ∈ (A ×ˢ S), (f sa.1) * (g sa.2) ) = 1  := 
          calc 
          ∑ sa ∈ (A ×ˢ S), (f sa.1)*(g sa.2)  = ∑ a ∈ A, ∑ s₂ ∈ S, (f a)*(g s₂) := 
               by apply Finset.sum_product 
          _ = ∑ a ∈ A, (f a) * (∑ s₂ ∈ S, (g s₂)) := by simp [Finset.mul_sum]  --Finset.sum_congr
          _ = ∑ a ∈ A, (f a) * 1 := by rw [h1]
          _ = ∑ a ∈ A, (f a) := by ring_nf
          _ = 1 := by rw[h2]

lemma prob_prod_hist {H : Finset (Hist m)} {A : Finset α} {S : Finset σ} 
          (t : Hist m → ℝ) (f : α → ℝ) (g : σ → ℝ) 
                 (h1 : ∑ s ∈ S, g s = 1) (h2 : ∑ a ∈ A, f a = 1): 
          (∑ has ∈ (H ×ˢ A ×ˢ S), (t has.1) * (f has.2.1 * g has.2.2) ) = (∑ h ∈ H, t h)  := 
          have innsum : (∑ sa ∈ (A ×ˢ S), (f sa.1) * (g sa.2) ) = 1 := by exact prob_prod f g h1 h2
          calc
            ∑ has ∈ (H ×ˢ A ×ˢ S), (t has.1) * (f has.2.1 * g has.2.2) = 
            ∑ h ∈ H, (∑ sa ∈ (A ×ˢ S), (t h) * (f sa.1 * g sa.2) ) := 
                  by apply Finset.sum_product 
            _ = ∑ h ∈ H, (t h) * (∑ sa ∈ (A ×ˢ S), (f sa.1 * g sa.2) ) := by simp [Finset.mul_sum]
            _ = ∑ h ∈ H, (t h) * 1 := Finset.sum_congr rfl fun x a ↦ congrArg (HMul.hMul (t x)) innsum
            _ = ∑ h ∈ H, (t h) := by ring_nf

/-- 
Show that history probabilities are actually a conditional probability 
distribution 
-/
theorem probability_dist [DecidableEq σ] (pre : Hist m) (π : Policy m) (T : ℕ) : 
            (∑ h ∈ PHist pre T, probability π h) = (probability π pre) := 
      match T with
        | Nat.zero =>   -- TODO: simplify, see? Finset.sum_eq_single, apply?
              --have h1 : PHist pre 0 = {pre} := rfl
              show (∑ h ∈ {pre}, probability π h) = (probability π pre) by simp
              --by refine Finset.sum_eq_single
        | Nat.succ t =>
              have h1 : (∑ h ∈ PHist pre t, probability π h) = (probability π pre) := 
                         by apply probability_dist
              let HAS := Finset.map emb_tuple2hist ((PHist pre t) ×ˢ m.AA ×ˢ m.SS)
              have h2 : PHist pre T = Finset.map emb_tuple2hist ((PHist pre t) ×ˢ m.AA ×ˢ m.SS)
 := rfl
              calc
                ∑ h ∈ PHist pre T, probability π h = ∑ h ∈ HAS, probability π h := by apply Finset.sum_congr
                



example : m.AA ×ˢ m.SS = Finset.product m.AA m.SS := rfl
example {h : Hist m} : PHist h 0 = {h} := rfl
example {h₀ : Hist m} {π : Policy m} [DecidableEq σ]: 
  (∑ h ∈ {h₀}, probability π h) = (probability π h₀) := by simp
  
/-

TODO:

1. Dynamic program for histories
2. Show that is the policy is Markov then also the value function is Markov
3. Show that histories are the PMF

-/
