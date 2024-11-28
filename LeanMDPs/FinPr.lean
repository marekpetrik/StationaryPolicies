import Mathlib.Data.Nat.Defs
import Mathlib.Data.Real.Basic 
import Mathlib.Data.NNReal.Basic


import Mathlib.Data.Finset.Image
import Mathlib.Logic.Function.Defs -- Function.Injective

universe u

open NNReal

variable {τ τ₁ τ₂: Type u} 
variable {ρ : Type u} [AddCommMonoid ρ]

#check Finset.sum_mul_sum

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
      ∑ ⟨t₁,t₂⟩ ∈ (T₁ ×ˢ T₂), (f t₁) * (g t₁ t₂) = 1 :=
    have h3 : ∀ t₁ ∈ T₁, 
                (∑ t₂ ∈ T₂, (f t₁)*(g t₁ t₂) 
                = (f t₁) * (∑ t₂ ∈ T₂, (g t₁ t₂)) ) := 
        fun t₁ _ ↦ Eq.symm (Finset.mul_sum T₂ (fun t₂ ↦ g t₁ t₂) (f t₁))
    calc 
        ∑ ⟨t₁,t₂⟩ ∈ (T₁ ×ˢ T₂), (f t₁)*(g t₁ t₂) 
        = ∑ t₁ ∈ T₁, ∑ t₂ ∈ T₂, (f t₁)*(g t₁ t₂) := 
                 Finset.sum_product T₁ T₂ fun x ↦ f x.1 * g x.1 x.2 
        _ = ∑ t₁ ∈ T₁, (f t₁) * (∑ t₂ ∈ T₂, (g t₁ t₂)) := 
                 Finset.sum_congr rfl h3
        _ = ∑ t₁ ∈ T₁, (f t₁) * 1 := 
                 Finset.sum_congr rfl (fun x a ↦ congrArg (fun y ↦ (f x)*y) (h2 x a))
        _ = ∑ a ∈ T₁, (f a) := Finset.sum_congr rfl (fun x _ ↦ MulOneClass.mul_one (f x))
        _ = 1 := h1
/--
Constructs a probability space as a product of a probability 
space and a dependent probability space.
-/
def FinP.product_dep {Ω₁ : Finset τ₁}
    (P₁ : FinP Ω₁) (Ω₂ : Finset τ₂) (p : τ₁ → τ₂ → ℝ≥0) 
    (h1: ∀ω₁ ∈ Ω₁, (∑ ω₂ ∈ Ω₂, p ω₁ ω₂) = 1) :
    FinP (Ω₁ ×ˢ Ω₂) := 
  {p := fun ⟨ω₁,ω₂⟩ ↦  
            P₁.p ω₁ * p ω₁ ω₂,
   sumsto := prob_prod_prob P₁.p p P₁.sumsto h1}
   

--def FinP.image {Ω : Finset τ} (P : FinP Ω) (f : τ ↪ τ₁) : (FinP (Ω.map f)) := 
--               {p := fun t₁ ↦ }

-- class ℙ 
-- class 𝔼 

/- --This is an unsuccessful attempt to define FinP as 
structure FinP {τ : Type u} (Ω : Finset τ): Type u where
  p : Ω → ℝ≥0
  sumsto : (∑ ω : Ω, p ω ) = 1
-- TODO: find suitable library replacements?
lemma inset₁ {α β : Type u} {p : α × β} {s : Finset α} {t : Finset β} : 
                  p ∈ s ×ˢ t → p.1 ∈ s := fun q ↦ (Finset.mem_product.mp q).left
lemma inset₂ {α β : Type u} {p : α × β} {s : Finset α} {t : Finset β} : 
                  p ∈ s ×ˢ t → p.2 ∈ t := fun q ↦ (Finset.mem_product.mp q).right
-- bijection between tuple and attached tuple                  
def inprod {s : Finset τ₁} {t : Finset τ₂} 
              (x : s ×ˢ t) : {x : τ₁ // x ∈ s} × {y : τ₂ // y ∈ t} :=
     ⟨ ⟨x.1.1, inset₁ x.2⟩, ⟨x.1.2, inset₂ x.2⟩ ⟩
def outprod {s : Finset τ₁} {t : Finset τ₂} 
              (x :  {x : τ₁ // x ∈ s} × {y : τ₂ // y ∈ t}) : (s ×ˢ t) :=
   ⟨ ⟨x.1.1, x.2.1⟩, Finset.mk_mem_product x.1.2 x.2.2⟩
lemma linv_inprod_outprod {s : Finset τ₁} {t : Finset τ₂} : 
          ∀ x : {x : τ₁ // x ∈ s} × {y : τ₂ // y ∈ t}, inprod (outprod x) = x := fun _ ↦ rfl
lemma linv_outprod_inprod {s : Finset τ₁} {t : Finset τ₂} : 
          ∀ x : s ×ˢ t, outprod (inprod x) = x := fun _ ↦ rfl

def sum_attach {α : Type u} [AddCommMonoid α] (T : Finset τ) (f : τ → α) : 
               ∃ g: T → α, (∑ x ∈ T, f x = ∑ x : T, g x) := 
    Exists.intro (λ x ↦ f x) (Eq.symm (Finset.sum_coe_sort T f))
-/
/-theorem sum_product_in (s : Finset τ₁) (t : Finset τ₂) 
        (f : {x:τ₁ // x∈s} × {y:τ₂ // y∈t} → ℝ≥0) :
    ∑ x : s ×ˢ t, f (inprod x) = ∑ x : s, ∑ y : t, f (x, y) := 
       calc
            ∑ x : s ×ˢ t, f (inprod x) = ∑ x ∈ s.attach ×ˢ t.attach, f x :=  by sorry
            _ = ∑ x : s, ∑ y : t, f (x, y) := Finset.sum_product s.attach t.attach f
-/
--      (Finset.sum_bijective ?e ?he (fun x ↦ ∑ y : { x // x ∈ t }, f (x, y)) (fun x ↦ f (inprod x)) ?h)

/-

lemma prob_prod_prob_attach {T₁ : Finset τ₁} {T₂ : Finset τ₂} 
      (f : T₁ → ℝ≥0) (g : T₁ → T₂ → ℝ≥0) 
      (h1 : ∑ t₁ : T₁, f t₁ = 1)  
      (h2 : ∀ t₁ : T₁,  ∑ t₂ : T₂, g t₁ t₂ = 1) : 
      ∑ ⟨⟨t₁,t₂⟩,p⟩ : (T₁ ×ˢ T₂), (f ⟨t₁,inset₁ p⟩) * (g ⟨t₁,inset₁ p⟩ ⟨t₂,inset₂ p⟩) = 1 := 
         let h4 := prob_prod_prob T₁.attach T₂.attach f g h1 (fun t₁ _ ↦ h2 t₁)
         by apply Finset.sum_nbij' inprod outprod ()  
/--
Constructs a probability space as a product of a probability 
space and a dependent probability space.
-/
def FinP.product_dep {Ω₁ : Finset τ₁}
    (P₁ : FinP Ω₁) (Ω₂ : Finset τ₂) (p : Ω₁ → Ω₂ → ℝ≥0) 
    (h1: ∀ω₁ : Ω₁, (∑ ω₂ : Ω₂, p ω₁ ω₂) = 1) :
    FinP (Ω₁ ×ˢ Ω₂) := 
  {p := fun ⟨⟨ω₁,ω₂⟩,q⟩ ↦  
            P₁.p ⟨ω₁, inset₁ q⟩ * p ⟨ω₁, inset₁ q⟩ ⟨ω₂, inset₂ q⟩,
   sumsto := prob_prod_prob P₁.p p P₁.sumsto h1}
   

lemma prob_prod_prob_attach {T₁ : Finset τ₁} {T₂ : Finset τ₂} 
      (f : T₁ → ℝ≥0) (g : T₁ → T₂ → ℝ≥0) 
      (h1 : ∑ t₁ : T₁, f t₁ = 1)  
      (h2 : ∀ t₁ : T₁,  ∑ t₂ : T₂, g t₁ t₂ = 1) : 
      ∑ ⟨⟨t₁,t₂⟩,p⟩ : (T₁ ×ˢ T₂), (f ⟨t₁,inset₁ p⟩) * (g ⟨t₁,inset₁ p⟩ ⟨t₂,inset₂ p⟩) = 1 := 
         let h4 := prob_prod_prob T₁.attach T₂.attach f g h1 (fun t₁ _ ↦ h2 t₁)
         by apply Finset.sum_nbij' inprod outprod ()  

-/   
