import LeanMDPs.Histories

-- TODO: is there a way to avoid these definitions here?
variable {σ α : Type}
variable [Inhabited σ] [Inhabited α]
variable [DecidableEq σ] [DecidableEq α]

variable {m : MDP σ α}


/-- 
Value function type for value functions that are

- history-dependent
- 

-/
def ValueHist_π (σ α : Type) := Hist σ α × ℕ → ℝ

/--
Defines the value function for a fixed history-dependent policy
-/
noncomputable 
def value_π (π : Policy m) : ValueHist_π σ α := 
      fun ⟨ pre, T ⟩ =>
        let ha := PHist m pre T
        ∑ (h ∈ ha), (fun h => (probability m π h) * (reward m h)) h
    -- the charater above is NOT Σ but is ∑ typed as \sum


def DP.value_π (π : Policy m)  :=  sorry

-- theorem value_hist_π_dp (m : MDP σ α) (π : Policy) (T : ℕ) :
              
