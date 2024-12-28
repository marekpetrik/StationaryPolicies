import Mathlib.Data.Nat.Defs
import Mathlib.Data.Real.Basic 
import Mathlib.Data.NNReal.Basic

import Mathlib.Data.Finset.Image
import Mathlib.Logic.Function.Defs -- Function.Injective

import Mathlib.Data.Finsupp.Indicator

--universe u

variable {τ τ₁ τ₂: Type } 
variable {T₁ : Finset τ₁} {T₂ : Finset τ₂}

open NNReal

/-- Finite probability distribution -/
structure Findist (Ω : Finset τ) : Type where
  p : τ → ℝ≥0 -- TODO: {p : ℝ // 0 ≤ p ∧ p ≤ 1}
  sumsto : (∑ ω ∈ Ω, p ω ) = 1
  
abbrev Δ : Finset τ → Type  := Findist

/-- Finite probability space -/
structure Finprob (τ : Type) : Type where
  Ω : Finset τ
  prob : Findist Ω

/-- Random variable defined on a finite probability space -/
structure Finrv (P : Finprob τ) (ρ : Type) : Type  where
  val : τ → ρ   -- actual value of the random variable
  
/- --------------------------------------------------------------- -/
namespace Finprob

-- This is the random variable output type
variable {ρ : Type} [HMul ℝ≥0 ρ ρ] [HMul ℕ ρ ρ] [AddCommMonoid ρ] 

/-- Handles the products in the expectation -/
instance HMul_NN_R : HMul ℝ≥0 ℝ ℝ where
  hMul := fun a b => ↑a * b

/-- Probability of a sample -/
def pr (pr : Finprob τ) (t : pr.Ω) := pr.prob.p t.1

/- ---------------------- Index -----------------/

/-- Boolean indicator function -/
def 𝕀 (cond : τ → Bool) (ω : τ) : ℕ := (cond ω).rec 0 1

/-- Indicator is 0 or 1 -/
theorem ind_zero_one (cond : τ → Bool) (ω : τ) : (𝕀 cond ω = 1) ∨ (𝕀 cond ω = 0) := 
  if h : (cond ω) then 
    let q := calc 
        𝕀 cond ω = Bool.rec 0 1 (cond ω) := rfl
        _ = Bool.rec 0 1 true := congrArg (Bool.rec 0 1) h
        _ = 1 := rfl
    Or.inl q
  else
    let q := calc 
        𝕀 cond ω = Bool.rec 0 1 (cond ω) := rfl
        _ = Bool.rec 0 1 false := congrArg (Bool.rec 0 1) (eq_false_of_ne_true h)
        _ = 0 := rfl
    Or.inr q
    
/-
theorem indicator_in_zero_one (cond : τ → Bool) : 
     ∀ω : τ, (𝕀 cond ω) ∈ ({0,1} : Finset ℝ≥0) := 
        fun ω => Bool.rec (by simp [Finset.mem_insert_self, Finset.pair_comm])
        (by simp [Finset.mem_insert_self, Finset.pair_comm]) (cond ω) 
-/

/- ---------------------- Expectation -----------------/

variable {P : Finprob τ}
variable {ν : Type} [DecidableEq ν] {V : Finset ν}

/-- Expectation of X -/
def expect (X : Finrv P ρ) : ρ := ∑ ω ∈ P.Ω, P.prob.p ω * X.val ω

notation "𝔼[" X "]" => expect X 

/-- Probability of B -/
def probability (B : Finrv P Bool) : ℝ≥0 := 
    let I : Finrv P ℝ≥0 := ⟨fun ω ↦ ↑(𝕀 B.val ω)⟩
    𝔼[I]
    
notation "ℙ[" B "]" => probability B 

/-- 
Expected value 𝔼[X|B] conditional on a Bool random variable 
IMPORTANT: conditional expectation for zero probability event is zero 
-/
noncomputable 
def expect_cnd (X : Finrv P ρ) (B : Finrv P Bool) : ρ := 
    let F : Finrv P ρ := ⟨fun ω ↦ 𝕀 B.val ω * X.val ω⟩
    ℙ[B]⁻¹ * 𝔼[F]
    
notation "𝔼[" X "|" B "]" => expect_cnd X B

/-- Random variable equality -/
def EqRD (Y : Finrv P V) (y : V) : Finrv P Bool := ⟨(fun ω ↦ Y.val ω == y)⟩ 

infix:50 " ᵣ== " => EqRD 

/-- Conditional expectation on a random variable --/
noncomputable 
def expect_cnd_rv (X : Finrv P ρ) (Y : Finrv P V) : Finrv P ρ := 
    ⟨fun ω ↦ 𝔼[X | Y ᵣ== Y.val ω ]⟩ 
    
notation "𝔼[" X "|ᵥ" Y "]" => expect_cnd_rv X Y


/- ------------ Law of the unconscious statistician ----------/

/-- Conditional version of the Law of the unconscious statistician -/
theorem unconscious_statistician_cnd (X : Finrv P ρ) (Y : Finrv P V) :
  ∀ ω ∈ P.Ω, (𝔼[X |ᵥ Y ]).val ω = ∑ y ∈ V, ℙ[Y ᵣ== (Y.val ω)]* 𝔼[X | Y ᵣ== (Y.val ω)]  :=
    sorry
  

/- ------------ Law of total expectation ----------/

theorem total_expectation (X : Finrv P ρ) (Y : Finrv P V) : 
  𝔼[ 𝔼[ X |ᵥ Y] ] = 𝔼[ X ] := 
        sorry

/- ---------------------- Supporting Results -----------------/


/-- Construct a dirac distribution -/
def dirac_ofsingleton (t : τ) : Findist {t} := 
  let p := fun _ ↦ 1
  {p := p, sumsto := Finset.sum_singleton p t}


/--
Product of a probability distribution with a dependent probability 
distributions is a probability distribution. 
-/
lemma prob_prod_prob (f : τ₁ → ℝ≥0) (g : τ₁ → τ₂ → ℝ≥0) 
      (h1 : ∑ t₁ ∈ T₁, f t₁ = 1) 
      (h2 : ∀ t₁ ∈ T₁,  ∑ t₂ ∈ T₂, g t₁ t₂ = 1) : 
      ∑ ⟨t₁,t₂⟩ ∈ (T₁ ×ˢ T₂), (f t₁) * (g t₁ t₂) = 1 :=
    calc 
        ∑ ⟨t₁,t₂⟩ ∈ (T₁ ×ˢ T₂), (f t₁)*(g t₁ t₂) 
        = ∑ t₁ ∈ T₁, ∑ t₂ ∈ T₂, (f t₁)*(g t₁ t₂) := by simp [Finset.sum_product] 
        _ = ∑ t₁ ∈ T₁, (f t₁) * (∑ t₂ ∈ T₂, (g t₁ t₂)) := by simp [Finset.sum_congr, Finset.mul_sum] 
        _ = ∑ t₁ ∈ T₁, (f t₁) := by simp_all [Finset.sum_congr, congrArg]
        _ = 1 := h1
        
/--
Probability distribution as a product of a probability distribution and a 
dependent probability distribution. -/
def product_dep {Ω₁ : Finset τ₁}
    (P₁ : Findist Ω₁) (Ω₂ : Finset τ₂) (p : τ₁ → τ₂ → ℝ≥0) 
    (h1: ∀ ω₁ ∈ Ω₁, (∑ ω₂ ∈ Ω₂, p ω₁ ω₂) = 1) :
    Findist (Ω₁ ×ˢ Ω₂) := 
  {p := fun ⟨ω₁,ω₂⟩ ↦ P₁.p ω₁ * p ω₁ ω₂,
   sumsto := prob_prod_prob P₁.p p P₁.sumsto h1}

/--
Constructs a probability space as a product of a probability 
space and a dependent probability space.
-/
def product_dep_pr {Ω₁ : Finset τ₁}
    (P₁ : Findist Ω₁) (Ω₂ : Finset τ₂) (Q : τ₁ → Findist Ω₂) : Findist (Ω₁ ×ˢ Ω₂) :=
      let g ω₁ ω₂ := (Q ω₁).p ω₂
      have h1 : ∀ ω₁ ∈ Ω₁, ∑ ω₂ ∈ Ω₂, g ω₁ ω₂ = 1 := fun ω₁ _ ↦ (Q ω₁).sumsto
      {p := fun ⟨ω₁,ω₂⟩ ↦ P₁.p ω₁ * (Q ω₁).p ω₂,
       sumsto := prob_prod_prob P₁.p (fun ω₁ => (Q ω₁).p) (P₁.sumsto) h1}
       

-- TODO: remove the need for passing in f_inv,
-- it should be sufficient to construct it because we only need it
-- to be a left inverse on T₂ = T₁.map f
/-- Embedding preserves a sum -/
lemma embed_preserve (T₁ : Finset τ₁) (p : τ₁ → ℝ≥0) (f : τ₁ ↪ τ₂) (f_linv : τ₂ → τ₁) 
            (h : Function.LeftInverse f_linv f) :
             ∑ t₂ ∈ (T₁.map f), (p ∘ f_linv) t₂ = ∑ t₁ ∈ T₁, p t₁ := 
        calc
           ∑ t₂ ∈ (T₁.map f), (p∘f_linv) t₂ = 
           ∑ t₁ ∈ T₁, (p∘f_linv∘f) t₁ := Finset.sum_map T₁ f (p ∘ f_linv)
           _ = ∑ t₁ ∈ T₁, p t₁ := Finset.sum_congr rfl fun x _ ↦ congrArg p (h x)  

-- TODO: remove the need for passing in f_inv,
-- see embed_preserve
/-- Embed the probability in a new space using e. Needs an inverse -/
def embed {Ω₁ : Finset τ₁} (P : Findist Ω₁) (e : τ₁ ↪ τ₂) (e_linv : τ₂ → τ₁) 
              (h : Function.LeftInverse e_linv e): Findist (Ω₁.map e) :=
          {p := fun t₂ ↦ (P.p∘e_linv) t₂,
           sumsto := Eq.trans (embed_preserve Ω₁ P.p e e_linv h) P.sumsto}
           
end Finprob
