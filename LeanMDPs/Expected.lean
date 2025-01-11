import LeanMDPs.Histories

--set_option diagnostics true
--set_option diagnostics.threshold 3

open NNReal
open Finprob
open MDPs

/- state -/
variable {σ : Type} [Inhabited σ] [DecidableEq σ] 
/- action -/
variable {α : Type} [Inhabited α] [DecidableEq α]
variable {M : MDP σ α}

section Objectives

-- Future generalization??
/- Generic objective definition -/
--def Objective (σ : Type) (α : Type) := MDP σ α → Type
/- General definition of an objective function -/
--class ObjectiveFun (o : Objective σ α) where
--  obj : Phr M → ℝ

/-- Finite horizon objective parameters -/
structure ObjectiveFH (M : MDP σ α) : Type where
  s₀ : M.S -- initial state
  T : ℕ -- horizon


/-- Objective function -/
def objective_fh (O : ObjectiveFH M) (π : Phr M) := 𝔼ₕ[ reward // O.s₀, π, O.T]

/-- An optimal policy πopt -/
def Optimal_fh (O : ObjectiveFH M) (πopt : Phr M) := ∀ π : Phr M, objective_fh O πopt ≥ objective_fh O π

/-- Value function type for value functions that are -/
def ValuesH (M : MDP σ α) : Type := Hist M → ℝ

/-- History-dependent value function -/
def hvalue_π (π : PolicyHR M) : ℕ → ValuesH M
  | Nat.zero => fun _ ↦ 0
  | Nat.succ t => fun h ↦ 𝔼ₕ[ reward // h, π, t.succ ] - reward h
  

-- TODO: This needs some thought to be defined properly
--def hvalue_opt : ℕ → ValuesH M
--    | Nat.zero => fun _ ↦ 0
--    | Nat.succ t => fun h => fun π ↦ hvalue_π π  


/-- A value-optimal policy πopt -/
def OptimalVF_fh (t : ℕ) (πopt : Phr M) := ∀ π : Phr M, ∀ h : Hist M, hvalue_π πopt t h ≥ hvalue_π π t h

theorem optimalvf_imp_optimal {O : ObjectiveFH M} (πopt : PolicyHR M) (opt : OptimalVF_fh O.T πopt) : 
                              (Optimal_fh O πopt) := 
        fun π => 
            calc
                objective_fh O πopt = 𝔼ₕ[ reward // O.s₀, πopt, O.T] := rfl
                _ = 𝔼ₕ[ reward // O.s₀, πopt, O.T ] - reward (O.s₀ : Hist M) + reward (O.s₀ : Hist M) := by ring
                _ = hvalue_π πopt O.T O.s₀ + reward (O.s₀ : Hist M) := 
                             by cases O.T; simp_all! [exph_zero_horizon_eq_zero]; simp_all! only [sub_add_cancel]
                _ ≥ objective_fh O π := sorry
          

end Objectives

section DPValueH

/-- Bellman operator on history-dependent value functions -/
def DPhπ (π : PolicyHR M) (vₜ : ValuesH M) : ValuesH M 
  | h => ∑ a ∈ M.A, ∑ s' ∈ M.S, ((π h).p a * (M.P h.last a).p s') * (M.r h.last a s' + vₜ h)

/-- Bellman operator on history-dependent value functions -/
def DPhopt (vₜ : ValuesH M) : ValuesH M 
  | h => let q a :=  ∑ s' ∈ M.S, (M.P h.last a).p s' * (M.r h.last a s' + vₜ h)
         M.A.sup' M.A_ne q

/-- Dynamic program value function, finite-horizon history dependent -/
def u_dp_π (π : PolicyHR M) : ℕ → ValuesH M 
  | Nat.zero => fun _ ↦ 0
  | Nat.succ t => DPhπ π (u_dp_π π t)


/-- Dynamic program value function, finite-horizon history dependent -/
def u_dp_opt  : ℕ → ValuesH M 
  | Nat.zero => fun _ ↦ 0
  | Nat.succ t => DPhopt (u_dp_opt t)
  
theorem dp_opt_ge_dp_pi (h : Hist M) (u₁ u₂ : ValuesH M) (uge : ∀h : Hist M, u₁ h ≥ u₂ h) :
        ∀h : Hist M, ∀π : PolicyHR M, DPhopt u₁ h ≥ DPhπ π u₂ h := sorry


theorem dph_correct_vf (π : PolicyHR M) (t : ℕ) (h : Hist M) : 
                      hvalue_π π t h = u_dp_π π t h := 
   match t with
     | Nat.zero => rfl
     | Nat.succ t => 
       let hp h' := dph_correct_vf π t h'
       sorry

theorem dph_opt_vf_opt (t : ℕ) : 
        ∀π : PolicyHR M, ∀ h : Hist M, u_dp_opt t h ≥ u_dp_π π t h := sorry 

end DPValueH
