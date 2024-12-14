import Mathlib.Data.Nat.Defs
import Mathlib.Data.Real.Basic 
import Mathlib.Data.NNReal.Basic


import Mathlib.Data.Finset.Image
import Mathlib.Logic.Function.Defs -- Function.Injective

import Mathlib.Data.Finsupp.Indicator

universe u

variable {τ τ₁ τ₂: Type u} 
variable {T₁ : Finset τ₁} {T₂ : Finset τ₂}

open NNReal

/-- Finite probability space -/
structure FinP (Ω : Finset τ) : Type u where
  p : τ → ℝ≥0
  sumsto : (∑ ω ∈ Ω, p ω ) = 1
  
abbrev Δ : Finset τ → Type u := FinP

structure FinPr (τ : Type u) : Type u where
  Ω : Finset τ
  prob : FinP Ω

namespace FinP

/-- Probability of a sample -/
def prob (pr : FinPr τ) (t : pr.Ω) := pr.prob.p t.1

abbrev ℙ : (pr : FinPr τ) → (t : pr.Ω) → ℝ≥0 := prob

/-- Expected value of random variable x -/
def expect (pr : FinPr τ) (x : τ → ℝ) : ℝ := ∑ ω ∈ pr.Ω, pr.prob.p ω * x ω 
  
abbrev 𝔼 : FinPr τ → (τ → ℝ) → ℝ := expect

/-- An indicator function τ → {0,1} of flexible type -/
def Indicator (τ : Type u)  --[OfNat ρ 0] [OfNat ρ 1] [Insert ρ (Finset ρ)]
               : Type u := τ → ({0,1} : Finset ℝ≥0)



def prob_cnd  (pr : FinPr τ) (c : Indicator τ) : ℝ≥0 :=
    ∑ ω : pr.Ω, (ℙ pr ω) * (c ω)

abbrev ℙc : FinPr τ → Indicator τ → ℝ≥0 := prob_cnd

variable (s : Finset τ)

/-- 
Conditional expected value E[x | c ] where x is an indicator function
IMPORTANT: conditional expectation for zero probability event is zero
-/
noncomputable
def expect_cnd (pr : FinPr τ) (x : τ → ℝ) (c : Indicator τ) : ℝ := 
    (∑ ω : pr.Ω, (ℙ pr ω) * (c ω) * x ω) /  ℙc pr c
    
noncomputable
abbrev 𝔼c : FinPr τ → (τ → ℝ) → Indicator τ → ℝ  := expect_cnd

/-- Conditional expectation on a random variable --/
noncomputable
def expect_cnd_rv {V : Finset τ₁} [DecidableEq τ₁] 
                  (pr : FinPr τ) (x : τ → ℝ) (y : τ → V) (ω : τ) : ℝ := 
  let ind: Indicator τ := fun ω' ↦ if y ω' = y ω then 
                          ⟨1, by simp [Finset.mem_insert_self, Finset.pair_comm]⟩ else 
                          ⟨0, by simp [Finset.mem_insert_self, Finset.pair_comm]⟩
  (∑ ω' : pr.Ω, (ℙ pr ω') * (ind ω') * x ω') /  ℙc pr ind

--theorem law_total_expectation 

/--
Product of a probability distribution with a dependent probability 
distributions is a probability distribution. 
-/
lemma prob_prod_prob (f : τ₁ → ℝ≥0) (g : τ₁ → τ₂ → ℝ≥0) 
      (h1 : ∑ t₁ ∈ T₁, f t₁ = 1) (h2 : ∀ t₁ ∈ T₁,  ∑ t₂ ∈ T₂, g t₁ t₂ = 1) : 
      ∑ ⟨t₁,t₂⟩ ∈ (T₁ ×ˢ T₂), (f t₁) * (g t₁ t₂) = 1 :=
    calc 
        ∑ ⟨t₁,t₂⟩ ∈ (T₁ ×ˢ T₂), (f t₁)*(g t₁ t₂) 
        = ∑ t₁ ∈ T₁, ∑ t₂ ∈ T₂, (f t₁)*(g t₁ t₂) := by simp [Finset.sum_product] 
        _ = ∑ t₁ ∈ T₁, (f t₁) * (∑ t₂ ∈ T₂, (g t₁ t₂)) := by simp [Finset.sum_congr, Finset.mul_sum] 
        _ = ∑ t₁ ∈ T₁, (f t₁) := by simp_all [Finset.sum_congr, congrArg]
        _ = 1 := h1
        
/-- Construct a dirac distribution -/
def dirac_ofsingleton (t : τ) : FinP {t} := 
  let p := fun _ ↦ 1
  {p := p, sumsto := Finset.sum_singleton p t}

/--
Probability distribution as a product of a probability distribution and a dependent probability 
distribution.
-/
def product_dep {Ω₁ : Finset τ₁}
    (P₁ : FinP Ω₁) (Ω₂ : Finset τ₂) (p : τ₁ → τ₂ → ℝ≥0) 
    (h1: ∀ ω₁ ∈ Ω₁, (∑ ω₂ ∈ Ω₂, p ω₁ ω₂) = 1) :
    FinP (Ω₁ ×ˢ Ω₂) := 
  {p := fun ⟨ω₁,ω₂⟩ ↦  
            P₁.p ω₁ * p ω₁ ω₂,
   sumsto := prob_prod_prob P₁.p p P₁.sumsto h1}

/--
Constructs a probability space as a product of a probability 
space and a dependent probability space.
-/
def product_dep_pr {Ω₁ : Finset τ₁}
    (P₁ : FinP Ω₁) (Ω₂ : Finset τ₂) (Q : τ₁ → FinP Ω₂) : FinP (Ω₁ ×ˢ Ω₂) :=
      let g ω₁ ω₂ := (Q ω₁).p ω₂
      have h1 : ∀ ω₁ ∈ Ω₁, ∑ ω₂ ∈ Ω₂, g ω₁ ω₂ = 1 := fun ω₁ _ ↦ (Q ω₁).sumsto
      {p := fun ⟨ω₁,ω₂⟩ ↦  
            P₁.p ω₁ * (Q ω₁).p ω₂,
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
def embed {Ω₁ : Finset τ₁} (P : FinP Ω₁) (e : τ₁ ↪ τ₂) (e_linv : τ₂ → τ₁) 
              (h : Function.LeftInverse e_linv e):
              FinP (Ω₁.map e) :=
          {p := fun t₂ ↦ (P.p∘e_linv) t₂,
           sumsto := Eq.trans (embed_preserve Ω₁ P.p e e_linv h) P.sumsto}
           
end FinP
