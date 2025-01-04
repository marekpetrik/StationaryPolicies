import LeanMDPs.Histories

--set_option diagnostics true
--set_option diagnostics.threshold 3

open NNReal

/- state -/
variable {σ : Type} [Inhabited σ] [DecidableEq σ] 
/- action -/
variable {α : Type} [Inhabited α] [DecidableEq α]
variable {M : MDP σ α}

open Finprob

/-- 
Value function type for value functions that are
- history-dependent
- for a specific policy
- and a horizon T
-/
def ValueH (M : MDP σ α) : Type := Hist M → ℝ

/-- Bellman operator on history-dependent value functions -/
def DPhπ (π : PolicyHR M) (vₜ : ValueH M) : ValueH M 
  | h => ∑ a ∈ M.A, ∑ s' ∈ M.S,  
           ((π h).p a * (M.P h.last a).p s') * (M.r h.last a s' + vₜ h)

/-- Finite-horizon value function definition, history dependent -/
def value_π (π : PolicyHR M) : ℕ → ValueH M
  | Nat.zero => fun _ ↦ 0
  | Nat.succ t => fun h ↦ 𝔼ₕ[ reward // h, π, t.succ ] 

/-- Dynamic program value function, finite-horizon history dependent -/
def value_dp_π (π : PolicyHR M) : ℕ → ValueH M 
  | Nat.zero => fun _ ↦ 0
  | Nat.succ t => DPhπ π (value_dp_π π t)

theorem dp_correct_vf (π : PolicyHR M) (T : ℕ) (h : Hist M) : 
                      value_π π T h = value_dp_π π T h := 
   match T with
     | Nat.zero => rfl
     | Nat.succ t => 
       let hp h' := dp_correct_vf π t h'
       sorry
