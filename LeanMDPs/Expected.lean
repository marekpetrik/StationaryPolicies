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
def ValueH (m : MDP σ α) : Type := Hist m → ℝ


/--
Defines an MDP Bellman operator on history-dependent value functions
-/
def DPπ (π : PolicyHR m) (vₜ : ValueH m) : ValueH m 
  | h => ∑ a ∈ m.A, ∑ s' ∈ m.S,  
           ((π h).p a * (m.P h.last a).p s') * (m.r h.last a s' + vₜ h)

/--
Defines the value function for a fixed history-dependent policy and a
given horizon
-/
def value_π (π : PolicyHR m) : ℕ → ValueH m
  | Nat.zero => fun _ ↦ 0
  | Nat.succ t => fun hₖ ↦ 𝔼ₕ hₖ π t.succ reward


def value_dp_π (π : PolicyHR m) : ℕ → ValueH m 
  | Nat.zero => fun _ ↦ 0
  | Nat.succ t => DPπ π (value_dp_π π t)

theorem dp_correct_vf  (π : PolicyHR m) (t : ℕ) (h : Hist m) : value_π π t h = value_dp_π π t h := 
   match t with
     | Nat.zero => rfl
     | Nat.succ t' => sorry
              
