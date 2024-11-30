import LeanMDPs.Histories

variable {σ α : Type}
variable [Inhabited σ] [Inhabited α]
variable [DecidableEq σ] [DecidableEq α]

variable {m : MDP σ α}

/-- 
Value function type for value functions that are

- history-dependent
- for a specific policy
- and a horizon T

-/
def ValueH (m : MDP σ α) := Hist m → ℝ


/--
Defines an MDP Bellman operator on history-dependent value functions
-/
def DP_π (π : Policy m) (vₜ : ValueH m) : ValueH m 
  | h => ∑ a ∈ m.A, ∑ s' ∈ m.S,  
           ((π h).p a * (m.P h.last a).p s') * (m.r h.last a s' + vₜ h)

/--
Defines the value function for a fixed history-dependent policy and a
given horizon
-/
noncomputable 
def value_π (π : Policy m) : ℕ → ValueH m
  | Nat.zero => fun _ ↦ 0
  | Nat.succ t => fun pre ↦ ∑ h ∈ PHist pre t.succ, probability π h * reward h


def value_dp_π (π : Policy m) : ℕ → ValueH m 
  | Nat.zero => fun _ ↦ 0
  | Nat.succ t => DP_π π (value_dp_π π t)

theorem dp_correct_vf  (π : Policy m) (t : ℕ) (h : Hist m) : value_π π t h = value_dp_π π t h := 
   match t with
     | Nat.zero => rfl
     | Nat.succ t' => sorry
              
