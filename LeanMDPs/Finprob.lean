import Mathlib.Data.Nat.Defs
import Mathlib.Data.Real.Basic 
import Mathlib.Data.NNReal.Basic

import Mathlib.Data.Finset.Image
import Mathlib.Logic.Function.Defs -- Function.Injective

import Mathlib.Data.Finsupp.Indicator

--universe u

variable {τ : Type} 

open NNReal

section Definitions

/-- Finite probability distribution -/
structure Findist (Ω : Finset τ) : Type where
  p : τ → ℝ≥0 -- TODO: {p : ℝ // 0 ≤ p ∧ p ≤ 1}
  sumsto : (∑ ω ∈ Ω, p ω ) = 1
  
abbrev Delta : Finset τ → Type := Findist
abbrev Δ : Finset τ → Type := Delta

/-- Finite probability space -/
structure Finprob (τ : Type) : Type where
  Ω : Finset τ
  prob : Findist Ω
  
/-- Random variable defined on a finite probability space -/
structure Finrv (P : Finprob τ) (ρ : Type) : Type  where
  val : τ → ρ   -- actual value of the random variable

end Definitions
  
/- --------------------------------------------------------------- -/
namespace Finprob

/-- Needed to handle a multiplication with 0 -/
class HMulZero (G : Type) extends HMul ℝ≥0 G G, OfNat G 0 where
  zero_mul : (a : G) → (0:ℝ≥0) * a = (0:G) 

instance HMulZeroReal : HMulZero ℝ where
  hMul := fun a b => ↑a * b
  zero_mul := zero_mul
  
instance HMulZeroRealPlus : HMulZero ℝ≥0 where
  hMul := fun a b => a * b
  zero_mul := zero_mul

-- This is the random variable output type
variable {ρ : Type} [HMulZero ρ] [AddCommMonoid ρ] 


/- ---------------------- Index -----------------/

/-- Boolean indicator function -/
@[reducible] def indicator (cond : Bool) : ℝ≥0 := cond.rec 0 1
abbrev 𝕀 : Bool → ℝ≥0 := indicator

/-- Indicator is 0 or 1 -/
theorem ind_zero_one (cond : τ → Bool) (ω : τ) : ((𝕀∘cond) ω = 1) ∨ ((𝕀∘cond) ω = 0) := 
  if h : (cond ω) then Or.inl (by simp [h])
  else Or.inr (by simp [h])

/- ---------------------- Expectation -----------------/

variable {P : Finprob τ}
variable {ν : Type} [DecidableEq ν] {V : Finset ν}

/-- Probability measure -/
@[reducible] def p (P : Finprob τ) (ω : τ) := P.prob.p ω


/-- Expectation of X -/
def expect (X : Finrv P ρ) : ρ := ∑ ω ∈ P.Ω, P.p ω * X.val ω

notation "𝔼[" X "]" => expect X 

/-- Probability of B -/
def probability (B : Finrv P Bool) : ℝ≥0 := 
    𝔼[ (⟨fun ω ↦ (𝕀∘B.val) ω⟩ : Finrv P ℝ≥0) ]
    
notation "ℙ[" B "]" => probability B 

example : (0:ℝ)⁻¹ = (0:ℝ) := inv_zero
/-- 
Expected value 𝔼[X|B] conditional on a Bool random variable 
IMPORTANT: conditional expectation for zero probability B is zero 
-/
@[reducible] noncomputable 
def expect_cnd (X : Finrv P ρ) (B : Finrv P Bool) : ρ := 
    ℙ[B]⁻¹ * 𝔼[ (⟨fun ω ↦ (𝕀∘B.val) ω * X.val ω⟩: Finrv P ρ ) ]
    
notation "𝔼[" X "|" B "]" => expect_cnd X B

/-- Conditional probability of B -/
@[reducible] noncomputable
def probability_cnd (B : Finrv P Bool) (C : Finrv P Bool) : ℝ≥0 := 
    𝔼[ ⟨fun ω ↦ (𝕀∘B.val) ω⟩ | C ]

notation "ℙ[" X "|" B "]" => probability_cnd X B

/-- Random variable equality -/
@[reducible] def EqRV {η : Type} [DecidableEq η] 
         (Y : Finrv P η) (y : η) : Finrv P Bool := ⟨fun ω ↦ Y.val ω == y⟩ 

infix:50 " ᵣ== " => EqRV 

@[reducible] def AndRV (B : Finrv P Bool) (C : Finrv P Bool) : Finrv P Bool :=
    ⟨fun ω ↦ B.val ω && C.val ω⟩

infix:50 " ∧ᵣ " => AndRV

@[reducible] def OrRV (B : Finrv P Bool) (C : Finrv P Bool) : Finrv P Bool :=
    ⟨fun ω ↦ B.val ω || C.val ω⟩

infix:50 " ∨ᵣ " => OrRV

/-- Expectation conditioned on a finite-valued random variable --/
@[reducible] noncomputable 
def expect_cnd_rv (X : Finrv P ρ) (Y : Finrv P V) : Finrv P ρ := 
    ⟨fun ω ↦ 𝔼[X | Y ᵣ== Y.val ω ]⟩ 
    
notation "𝔼[" X "|ᵥ" Y "]" => expect_cnd_rv X Y


/- --------- Construction --------------/
section Construction


/-- Construct a dirac distribution -/
def dirac_ofsingleton (t : τ) : Findist {t} := 
  let p := fun _ ↦ 1
  {p := p, sumsto := Finset.sum_singleton p t}


/-- Dirac distribution over T with P[t] = 1 -/
def dirac_dist [DecidableEq τ] (T : Finset τ) (t : T) : Findist T := 
  let p : τ → ℝ≥0 := fun x ↦ if x = t then 1 else 0
  -- proof it sums to 1
  let S : Finset τ := {t.1}
  have h1 : S ⊆ T := Finset.singleton_subset_iff.mpr t.2
  have h2 (x : τ) (out: x ∉ S) : p x = 0 :=  
    if hh: x = t then (out (Finset.mem_singleton.mpr hh)).rec
    else by simp [hh, p]
  have h3 : ∑ x ∈ T, p x = 1 := calc
    ∑ x ∈ T, p x = ∑ x ∈ S, p x := Eq.symm (Finset.sum_subset h1 fun x a ↦ h2 x)
    _ = p t := Finset.sum_singleton p t
    _ = 1 := by simp [p]
  ⟨p, h3⟩

end Construction

/- --------- Basic properties ----------/

section BasicProperties

variable (X : Finrv P ρ) (B : Finrv P Bool) (C : Finrv P Bool) (Y : Finrv P V)
variable (y : V)

lemma ind_and_eq_prod_ind : ∀ ω ∈ P.Ω, 𝕀 ((B ∧ᵣ C).val ω) = (𝕀∘B.val) ω * (𝕀∘C.val) ω := sorry

theorem exp_zero_cond (zero : ℙ[C] = 0) : 𝔼[X | C] = 0 :=
      let izero : ℙ[C]⁻¹ = 0 := Eq.symm (zero_eq_inv.mpr (Eq.symm zero))
      let F : Finrv P ρ := ⟨fun ω ↦ (𝕀∘C.val) ω * X.val ω⟩
      calc 
        𝔼[X | C] = ℙ[C]⁻¹ * 𝔼[ (⟨fun ω ↦ (𝕀∘C.val) ω * X.val ω⟩: Finrv P ρ ) ] := rfl
        _ = ℙ[C]⁻¹ * 𝔼[F] := rfl
        _ = (0:ℝ≥0) * 𝔼[F] := by rw[izero]
        _ = (0:ρ) := by rw[HMulZero.zero_mul]

theorem prob_zero_cond (zero : ℙ[C] = 0) : ℙ[B | C] = 0 := 
  exp_zero_cond ((⟨fun ω ↦ ↑((𝕀∘B.val) ω)⟩ : Finrv P ℝ≥0))  C zero 

theorem prob_eq_prob_cond_prod : ℙ[B ∧ᵣ C] = ℙ[B | C] * ℙ[C] := sorry 

lemma prob_ge_measure : ∀ ω ∈ P.Ω, ℙ[Y ᵣ== (Y.val ω)] ≥ P.p ω := sorry

end BasicProperties

/- --------- Laws of the unconscious statistician ----------/

section Unconscious

variable (X : Finrv P ρ) (B : Finrv P Bool) (C : Finrv P Bool) (Y : Finrv P V)

/-- Law of the unconscious statistician -/
theorem exp_sum_val [DecidableEq ρ] :
        𝔼[ X ] = ∑ x ∈ (P.Ω.image X.val), ℙ[ X ᵣ== x ] * x := sorry

/-- Law of the unconscious statistician, conditional -/
theorem exp_sum_val_cnd [DecidableEq ρ] :
        𝔼[ X | B ] = ∑ x ∈ (P.Ω.image X.val), ℙ[ X ᵣ== x | B ] * x := sorry

/-- Law of the unconscious statistician, conditional random variable -/
theorem exp_sum_val_cnd_rv  :
  ∀ ω ∈ P.Ω, (𝔼[X |ᵥ Y ]).val ω = ∑ y ∈ V, ℙ[Y ᵣ== (Y.val ω)] * 𝔼[X | Y ᵣ== (Y.val ω)]  :=
    sorry

end Unconscious

/- ------------ Law of total expectation ----------/

section Total

variable (X : Finrv P ρ) (B : Finrv P Bool) (C : Finrv P Bool) (Y : Finrv P V)

theorem total_probability : ℙ[ B ] = ∑ y : V, ℙ[Y ᵣ==y ] * ℙ[ B | Y ᵣ== y] := sorry

theorem total_expectation : 𝔼[ 𝔼[ X |ᵥ Y] ] = 𝔼[ X ] := sorry

end Total 

/- ---------------------- Supporting Results -----------------/


section SupportingResults

variable {τ₁ τ₂: Type }
variable {T₁ : Finset τ₁} {T₂ : Finset τ₂}

  
/-- Product of a probability distribution with a dependent probability 
distributions is a probability distribution. -/
theorem prob_prod_prob (f : τ₁ → ℝ≥0) (g : τ₁ → τ₂ → ℝ≥0) 
      (h1 : ∑ t₁ ∈ T₁, f t₁ = 1) 
      (h2 : ∀ t₁ ∈ T₁,  ∑ t₂ ∈ T₂, g t₁ t₂ = 1) : 
      ∑ ⟨t₁,t₂⟩ ∈ (T₁ ×ˢ T₂), (f t₁) * (g t₁ t₂) = 1 :=
    calc
        ∑ ⟨t₁,t₂⟩ ∈ (T₁ ×ˢ T₂), f t₁ * g t₁ t₂ 
        = ∑ t₁ ∈ T₁, ∑ t₂ ∈ T₂, f t₁ * g t₁ t₂ := by simp only [Finset.sum_product] 
        _ = ∑ t₁ ∈ T₁, f t₁ * (∑ t₂ ∈ T₂, (g t₁ t₂)) := by simp only [Finset.mul_sum] 
        _ = ∑ t₁ ∈ T₁, f t₁ := by simp_all only [mul_one]
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
           
end SupportingResults

end Finprob
