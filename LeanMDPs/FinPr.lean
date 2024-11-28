import Mathlib.Data.Nat.Defs
import Mathlib.Data.Real.Basic 
import Mathlib.Data.NNReal.Basic

universe u

open NNReal

variable {τ τ₁ τ₂: Type u} 

/--
Finite probability space
-/
structure FinP {τ : Type u} (Ω : Finset τ): Type u where
  p : τ → ℝ≥0
  sumsto : (∑ ω ∈ Ω, p ω ) = 1

/--
Product of a probability distribution with a dependent probability 
distributions is a probability distribution. 
-/
lemma prob_prod_prob {T₁ : Finset τ₁} {T₂ : Finset τ₂} 
      (f : τ₁ → ℝ≥0) (g : τ₁ → τ₂ → ℝ≥0) 
      (h1 : ∑ t₁ ∈ T₁, f t₁ = 1)  
      (h2 : ∀ t₁ ∈ T₁,  ∑ t₂ ∈ T₂, g t₁ t₂ = 1) : 
      (∑ ⟨t₁,t₂⟩ ∈ (T₁ ×ˢ T₂), (f t₁) * (g t₁ t₂) ) = 1  :=

    have h3 : ∀ t₁ ∈ T₁, 
                ∑ t₂ ∈ T₂, (f t₁)*(g t₁ t₂) = (f t₁) * (∑ t₂ ∈ T₂, (g t₁ t₂)) := 
        fun t₁ a ↦ Eq.symm (Finset.mul_sum T₂ (g t₁) (f t₁))
    calc 
        ∑ ⟨t₁,t₂⟩ ∈ (T₁ ×ˢ T₂), (f t₁)*(g t₁ t₂) 
        = ∑ t₁ ∈ T₁, ∑ t₂ ∈ T₂, (f t₁)*(g t₁ t₂) := 
                 Finset.sum_product T₁ T₂ fun x ↦ f x.1 * g x.1 x.2 
        _ = ∑ t₁ ∈ T₁, (f t₁) * (∑ t₂ ∈ T₂, (g t₁ t₂)) := Finset.sum_congr rfl h3
        _ = ∑ t₁ ∈ T₁, (f t₁) * 1 := 
                 Finset.sum_congr rfl (fun x a ↦ congrArg (fun y ↦ (f x)*y) (h2 x a))
        _ = ∑ a ∈ T₁, (f a) := by ring_nf
        _ = 1 := h1

/--
Constructs a probability space as a product of a probability 
space and a dependent probability space.
-/
def FinP.product_dep {Ω₁ : Finset τ₁}
    (P₁ : FinP Ω₁) (Ω₂ : Finset τ₂) (p : τ₁ → τ₂ → ℝ≥0) 
                     (h1: ∀ω₁ ∈ Ω₁, (∑ ω₂ ∈ Ω₂, p ω₁ ω₂) = 1): 
                           FinP (Ω₁ ×ˢ Ω₂) := 
  {p := fun ⟨ω₁,ω₂⟩ ↦ P₁.p ω₁ * p ω₁ ω₂,
   sumsto := prob_prod_prob P₁.p p P₁.sumsto h1}
   



-- class ℙ 
-- class 𝔼 
