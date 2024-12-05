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
variable [Inhabited σ] [Inhabited α]

open NNReal -- for ℝ≥0 notation

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
  P : σ → α → (FinP S)
  /-- reward function s, a, s' -/
  r : σ → α → σ → ℝ
  /-- initial distribution -/
  μ : FinP S

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


/--
Creates new histories from combinations of shorter histories
and states and actions.
-/
def tuple2ctuple : Hist m × α × σ → (Hist m × α) × σ
  | ⟨h, ⟨a, s⟩⟩ => ⟨⟨h, a⟩, s⟩

def ctuple2tuple : (Hist m × α) × σ → Hist m × α × σ
  | ⟨⟨h, a⟩, s⟩ => ⟨h, ⟨a, s⟩⟩

/-- History append has a left inverse to show it is an embedding. -/
lemma linv_hist2ctuple_ctuple2hist : 
         Function.LeftInverse ((tuple2ctuple ∘ hist2tuple) : Hist m → (Hist m × α) × σ)
                              (tuple2hist ∘ ctuple2tuple) := fun _ => rfl

def emb_ctuple2hist : (Hist m × α) × σ ↪ Hist m :=
  { toFun := tuple2hist ∘ ctuple2tuple,
    inj' := Function.LeftInverse.injective linv_hist2ctuple_ctuple2hist}

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
def Policy (m : MDP σ α) := Hist m → FinP m.A

/-- 
Set of all policies that follow history pre.
Note that this is just a definition of the set and not a specific instance of the set

T is the number of steps beyond the history pre
-/
def PHist (pre : Hist m) (T : ℕ) : Finset (Hist m) := 
    match T with 
      | Nat.zero => {pre}
      | Nat.succ t =>  ((PHist pre t) ×ˢ m.A ×ˢ m.S).map emb_tuple2hist 


noncomputable
def PH (pre : Hist m) (π : Policy m) (T : ℕ) : FinP (PHist pre T) :=
  match T with 
    | Nat.zero => dirac_ofsingleton pre
    | Nat.succ t => 
      let prev := PH pre π t -- previous history
      -- probability of the history
      let f h (as : α × σ) := ((π h).p as.1 * (m.P h.last as.1).p as.2)
      let p : Hist m → ℝ≥0 
        | Hist.init _ => 0
        | Hist.prev h a s => prev.p h * f h ⟨a,s⟩
      let sumsto_as (h : Hist m) : ∑ ⟨a, s⟩ ∈ m.A ×ˢ m.S, f h ⟨a,s⟩ = 1 :=
          prob_prod_prob (π h).p (fun a =>(m.P h.last a).p ) 
                         (π h).sumsto (fun a _ => (m.P h.last a).sumsto)
      let sumsto : ∑ ⟨h,a,s⟩ ∈ ((PHist pre t) ×ˢ m.A ×ˢ m.S), f h ⟨a,s⟩ = 1 := sorry
      let HAS := ((PHist pre t) ×ˢ m.A ×ˢ m.S).map emb_tuple2hist
      let sumsto_fin : ∑ h ∈ HAS, p h  = 1 := sorry
      {p := p, sumsto := sumsto_fin}
      --let phist := PH pre π t
      --let phista := product_dep_pr phist m.A π 
      --let phistas := product_dep_pr phista m.S (fun ⟨h,a⟩ => m.P h.last a)
      --embed phistas emb_ctuple2hist (tuple2ctuple ∘ hist2tuple) linv_hist2ctuple_ctuple2hist

/--
Computes the probability of a history
-/
noncomputable def probability (π : Policy m) : Hist m → ℝ≥0 
      | Hist.init s => m.μ.p s
      | Hist.prev hp a s' => probability π hp * ((π hp).p a * (m.P hp.last a).p s')  
 
noncomputable def probability_has (π : Policy m) : Hist m × α × σ → ℝ≥0 
      | ⟨h,a,s⟩ => probability π h * ((π h).p a * (m.P h.last a).p s)

lemma hist_prob (π : Policy m) [DecidableEq σ]: 
       ∀ has, probability π (emb_tuple2hist has) = probability_has π has := fun _ => rfl

noncomputable def probability_pre [DecidableEq σ] (π : Policy m) : Hist m → ℝ≥0 
      | Hist.init s => m.μ.p s
      | Hist.prev hp a s' => probability π hp * ((π hp).p a * (m.P hp.last a).p s')  

/-- Compute the probability of a history 
-/
def ℙₕ (pre : Hist m) (π : Policy m) (T : ℕ)  : FinP (PHist pre T) := sorry

/--
Computes the reward of a history
-/
noncomputable def reward : Hist m → ℝ 
    | Hist.init _ => 0.
    | Hist.prev hp a s' => (m.r hp.last a s') + (reward hp)  

lemma prob_prod {A : Finset α} {S : Finset σ} 
      (f : α → ℝ≥0) (g : α → σ → ℝ≥0) (h1 : ∀ a : α, ∑ s ∈ S, g a s = 1) (h2 : ∑ a ∈ A, f a = 1): 
          (∑ ⟨a,s⟩ ∈ (A ×ˢ S), (f a) * (g a s) ) = 1  := 
          calc 
          ∑ ⟨a,s⟩ ∈ (A ×ˢ S), (f a)*(g a s)  = ∑ a ∈ A, ∑ s₂ ∈ S, (f a)*(g a s₂) := 
                 Finset.sum_product A S fun x ↦ f x.1 * g x.1 x.2 --by apply Finset.sum_product 
          _ = ∑ a ∈ A, (f a) * (∑ s₂ ∈ S, (g a s₂)) := by simp [Finset.mul_sum]  --Finset.sum_congr
          _ = ∑ a ∈ A, (f a) * 1 := 
                Finset.sum_congr rfl fun x a ↦ congrArg (fun y => (f x)*y) (h1 x)
          _ = ∑ a ∈ A, (f a) := by ring_nf
          _ = 1 := h2

lemma prob_prod_hist {H : Finset (Hist m)} {A : Finset α} {S : Finset σ} (t : Hist m → ℝ≥0) 
      (f : Hist m → α → ℝ≥0) (g : Hist m → α → σ → ℝ≥0) 
                (h1 : ∀ h : Hist m, ∀ a : α, ∑ s ∈ S, g h a s = 1) 
                (h2 : ∀ h : Hist m, ∑ a ∈ A, f h a = 1): 
(∑ ⟨h,a,s⟩ ∈ (H ×ˢ A ×ˢ S), (t h) * (f h a * g h a s) ) = (∑ h ∈ H, t h)  := 
          have innsum {h : Hist m} : (∑ sa ∈ (A ×ˢ S), (f h sa.1) * (g h sa.1 sa.2) ) = 1 := 
                      by exact prob_prod (f h) (g h) (h1 h) (h2 h)
          calc
            ∑ ⟨h,a,s⟩ ∈ (H ×ˢ A ×ˢ S), (t h) * (f h a * g h a s) = 
            ∑ h ∈ H, (∑ sa ∈ (A ×ˢ S), (t h) * (f h sa.1 * g h sa.1 sa.2) ) := 
                  by apply Finset.sum_product 
            _ = ∑ h ∈ H, (t h) * (∑ ⟨a,s⟩ ∈ (A ×ˢ S), (f h a * g h a s) ) := 
                  by simp [Finset.mul_sum]
            _ = ∑ h ∈ H, (t h) * 1 := 
                  Finset.sum_congr rfl fun x a ↦ congrArg (HMul.hMul (t x)) innsum
            _ = ∑ h ∈ H, (t h) := by ring_nf


lemma prob_prod_ha {H : Finset (Hist m)} {π : Policy m}  [Inhabited (Hist m)]: 
    ∑ has ∈ (H ×ˢ m.A ×ˢ m.S), (probability_has π has) = ∑ h ∈ H, probability π h :=
      prob_prod_hist (m:=m) 
        (probability π) (fun h a => (π h).p a) (fun h a s => (m.P h.last a).p s)
        (fun h a ↦ (m.P h.last a).sumsto) (fun h => (π h).sumsto)
    
/-- 
Show that history probabilities are actually a conditional probability 
distributions
-/
theorem probability_dist [Inhabited (Hist m)] [DecidableEq σ] (pre : Hist m) (π : Policy m) (T : ℕ) : 
            (∑ h ∈ PHist pre T, probability π h) = (probability π pre) := 
      match T with
        --base case
        | Nat.zero => Finset.sum_singleton (probability π) pre
        -- inductive case
        | Nat.succ t =>
              -- h1 is the inductive assumption
              have h1 : (∑ h ∈ PHist pre t, probability π h) = (probability π pre) := 
                         by apply probability_dist
              let HAS := ((PHist pre t) ×ˢ m.A ×ˢ m.S).map emb_tuple2hist
              calc
                ∑ h ∈ PHist pre t.succ, probability π h = 
                  ∑ h ∈ HAS, probability π h := rfl
                _ = ∑ has ∈ ((PHist pre t) ×ˢ m.A ×ˢ m.S), (probability π) (emb_tuple2hist has) :=
                      by apply Finset.sum_map
                _ = ∑ has ∈ ((PHist pre t) ×ˢ m.A ×ˢ m.S), (probability_has π has) := 
                        by simp [hist_prob]
                _ = ∑ h ∈ (PHist pre t), probability π h := by apply prob_prod_ha
                _ = probability π pre := by apply h1


/-

TODO:

1. Dynamic program for histories
2. Show that is the policy is Markov then also the value function is Markov

-/
