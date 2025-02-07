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


/-- Finite probability distribution on a list (allows for duplicates) -/
structure Findist (Ω : List τ) : Type where
  p : τ → ℝ 
  gezero : ∀ω ∈ Ω, p ω ≥ 0 -- separate for convenience
  sumsto : (Ω.map p).sum = 1
  
abbrev Delta : List τ → Type := Findist
abbrev Δ : List τ → Type := Delta

/-- Finite probability space -/
structure Finprob (τ : Type) : Type where
  Ω : List τ
  prob : Findist Ω
  
/-- Random variable defined on a finite probability space -/
structure Finrv (P : Finprob τ) (ρ : Type) : Type  where
  val : τ → ρ   -- actual value of the random variable

end Definitions


section Manipulation

variable {P : Finprob τ}

/-- Probability measure -/
@[reducible] def Finprob.p (P : Finprob τ) (ω : τ) := P.prob.p ω

/-
def Finprob.filter_zero (P : Finprob τ) : Finprob τ :=
  let Ω' := P.Ω.filter (fun ω ↦ P.p ω ≠ 0)
  let sumsto := calc 
    ∑ ω ∈ Ω', P.p ω = ∑ ω ∈ P.Ω, P.p ω := Finset.sum_filter_ne_zero P.Ω
    _ = 1 := P.prob.sumsto
  ⟨Ω', ⟨P.prob.p, sumsto⟩⟩
-/
#check Finset.sum_filter_ne_zero

/-- Checks if an element is supported -/
noncomputable
def Finprob.issupp (P : Finprob τ) (ω : τ) := !decide (P.p ω = 0)

/-- Removing zero probabilities does not affect sum -/
lemma list_filter_zero_sum_eq_sum (L : List τ) (p : τ → ℝ) : 
  ((L.filter (fun ω => !decide (p ω = 0))).map p).sum = (L.map p).sum := by 
    induction L with
    | nil => rfl
    | cons head tail => by_cases p head = 0; simp_all!; simp_all!

/-- Removes elements of Ω that have zero probability -/
noncomputable
def Finprob.filter_zero (P : Finprob τ) : Finprob τ :=
  let Ω₁ := P.Ω.filter P.issupp
  let sumsto : (Ω₁.map P.prob.p).sum = 1 := by 
      simp[Ω₁]; rewrite[←P.prob.sumsto]; 
      apply list_filter_zero_sum_eq_sum P.Ω P.prob.p
  let gezero := fun ω a ↦ P.prob.gezero ω (List.mem_of_mem_filter a)
  ⟨Ω₁, ⟨P.prob.p, gezero , sumsto⟩⟩

variable {Q : Finprob τ}

theorem prob_filtered_positive (h : Q = P.filter_zero) : ∀ω ∈ Q.Ω, Q.p ω > 0 := 
  by intro ω incnd; rw [h] at incnd; rw [h]
     have nezero := ((List.mem_filter).mp incnd).2
     have gezero := P.filter_zero.prob.gezero ω incnd       
     simp [Finprob.issupp,Finprob.p] at nezero
     exact lt_of_le_of_ne gezero (Ne.symm nezero)

noncomputable
def Finrv.filter_zero {ε : Type} (X : Finrv P ε) : Finrv (P.filter_zero) ε := ⟨X.val⟩

def Finprob.supp (P : Finprob τ) (ω : τ) := 0 < P.p ω 

end Manipulation
  
/- --------------------------------------------------------------- -/
namespace Finprob


/- ---------------------- Index -----------------/

/-- Boolean indicator function -/
@[reducible] def indicator (cond : Bool) : ℝ≥0 := cond.rec 0 1
abbrev 𝕀 : Bool → ℝ≥0 := indicator

/-- Indicator is 0 or 1 -/
theorem ind_zero_one (cond : τ → Bool) (ω : τ) : ((𝕀∘cond) ω = 1) ∨ ((𝕀∘cond) ω = 0) := 
  if h : (cond ω) then Or.inl (by simp [h])
  else Or.inr (by simp [h])

theorem ind_ge_zero (cond : τ → Bool) (ω : τ) : 0 ≤ (𝕀∘cond) ω := zero_le ((𝕀 ∘ cond) ω)
  

/- ---------------------- Expectation -----------------/

variable {P : Finprob τ}
variable {ν : Type} [DecidableEq ν] {V : Finset ν}

/-- Probability of B -/
def probability (B : Finrv P Bool) : ℝ≥0 := 
  let X : Finrv P ℝ := ⟨fun ω ↦ 𝕀 (B.val ω) ⟩  
  let gezero ω _ : 0 ≤ X.val ω := ind_ge_zero B.val ω
  ⟨𝔼[X], exp_ge_zero gezero⟩
    
notation "ℙ[" B "]" => probability B 

/-- Expectation of X -/
def expect (X : Finrv P ℝ) : ℝ := ∑ ω ∈ P.Ω, P.p ω * X.val ω

notation "𝔼[" X "]" => expect X 


example {A : List ν} {f : ν → ℝ}  {c : ℝ} (le : ∀a ∈ A, f a ≤ c) : (A.map f).sum ≤ c * A.length:= 
  by induction A
     · simp only [List.map_nil, List.sum_nil, List.length_nil, Nat.cast_zero, mul_zero, le_refl]
     · simp_all!
       linarith

example {A : List τ} {f : τ → ℝ} {p : τ → ℝ} {c : ℝ} 
      (nz : ∀ a ∈ A, p a ≥ 0) (le : ∀a ∈ A, f a ≤ c) : 
  (A.map (fun ω ↦ p ω * f ω)).sum ≤ c * (A.map p).sum := 
    by induction A; simp; simp_all; nlinarith 
          
example : ∀ (n : Nat), LE.le (Nat.succ n) 0 → False
  | 0      => nofun
  | Nat.succ _ => nofun

example : 0 = 1 → False := fun e => Nat.not_succ_le_zero 0 (Nat.le_of_eq e.symm)

--example {X : Finrv P ℝ} : expect X = 

#check List.Sublist.sum_le_sum 
#check List.Forall₂.sum_le_sum 
#check (· ≤ ·)


theorem exp_ge_zero {X : Finrv P ℝ} (gezero : ∀ω ∈ P.Ω, 0 ≤ X.val ω) : 0 ≤ 𝔼[X] := sorry --by induction P.Ω.card; simp_all!

example : (0:ℝ)⁻¹ = (0:ℝ) := inv_zero
/-- 
Expected value 𝔼[X|B] conditional on a Bool random variable 
IMPORTANT: conditional expectation for zero probability B is zero 
-/
@[reducible] noncomputable 
def expect_cnd (X : Finrv P ℝ) (B : Finrv P Bool) : ℝ := 
    ℙ[B]⁻¹ * 𝔼[ (⟨fun ω ↦ (𝕀∘B.val) ω * X.val ω⟩ : Finrv P ℝ ) ]
    
notation "𝔼[" X "|" B "]" => expect_cnd X B

theorem exp_cnd_ge_zero {X : Finrv P ℝ} {B : Finrv P Bool} 
                        (gezero : ∀ ω ∈ P.Ω, 0 ≤ X.val ω) : 0 ≤ 𝔼[ X | B ] := sorry

/-- Conditional probability of B -/
@[reducible] noncomputable
def probability_cnd (B : Finrv P Bool) (C : Finrv P Bool) : ℝ≥0 := 
    let X : Finrv P ℝ := ⟨fun ω ↦ (𝕀∘B.val) ω⟩  
    let gezero ω _ : 0 ≤ X.val ω := ind_ge_zero B.val ω
    ⟨𝔼[ X | C ], exp_cnd_ge_zero gezero⟩

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
def expect_cnd_rv (X : Finrv P ℝ) (Y : Finrv P V) : Finrv P ℝ := 
    ⟨fun ω ↦ 𝔼[X | Y ᵣ== Y.val ω ]⟩ 
    
notation "𝔼[" X "|ᵥ" Y "]" => expect_cnd_rv X Y

/- --------- Operations with random variables --------------/
section Operations

instance instConstRV : Coe ℝ (Finrv P ℝ) where
  coe c := ⟨fun _ ↦ c⟩
  
instance instRVadd : HAdd (Finrv P ℝ) (Finrv P ℝ) (Finrv P ℝ) where
  hAdd l r := ⟨fun ω ↦ l.val ω + r.val ω⟩
 
instance instRVmul [HMul ℝ ℝ ℝ] : HMul ℝ (Finrv P ℝ) (Finrv P ℝ) where
  hMul l r := ⟨fun ω ↦ l * r.val ω⟩


end Operations


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

variable {X : Finrv P ℝ} { Z : Finrv P ℝ } { B : Finrv P Bool } { C : Finrv P Bool } { Y : Finrv P V }
variable (y : V)

lemma ind_and_eq_prod_ind : ∀ ω ∈ P.Ω, 𝕀 ((B ∧ᵣ C).val ω) = (𝕀∘B.val) ω * (𝕀∘C.val) ω := sorry

theorem exp_zero_cond (zero : ℙ[C] = 0) : 𝔼[X | C] = 0 :=
      let izero : ℙ[C]⁻¹ = 0 := Eq.symm (zero_eq_inv.mpr (Eq.symm zero))
      let F : Finrv P ℝ := ⟨fun ω ↦ (𝕀∘C.val) ω * X.val ω⟩
      calc 
        𝔼[X | C] = ℙ[C]⁻¹ * 𝔼[ (⟨fun ω ↦ (𝕀∘C.val) ω * X.val ω⟩: Finrv P ℝ ) ] := rfl
        _ = ℙ[C]⁻¹ * 𝔼[F] := rfl
        _ = (0:ℝ≥0) * 𝔼[F] := by rw[izero]
        _ = 0 := mul_eq_zero_of_left rfl 𝔼[F]

theorem prob_zero_cond (zero : ℙ[C] = 0) : ℙ[B | C] = 0 := sorry


theorem prob_eq_prob_cond_prod : ℙ[B ∧ᵣ C] = ℙ[B | C] * ℙ[C] := sorry 

theorem prob_ge_measure : ∀ ω ∈ P.Ω, ℙ[Y ᵣ== (Y.val ω)] ≥ P.p ω := sorry


theorem exp_omit_zero : 𝔼[ X ] = 𝔼[ X.filter_zero ] := 
  let f ω := P.p ω ≠ 0
  let ne : ∀ω ∈ P.Ω, ((P.p ω * X.val ω) ≠ 0) → f ω := fun ω _ a ↦ left_ne_zero_of_smul a
  calc
    𝔼[ X ] = ∑ ω ∈ P.Ω, P.p ω * X.val ω := rfl
    _ = ∑ ω ∈ P.Ω.filter f, P.p ω * X.val ω := 
          (Finset.sum_filter_of_ne ne).symm
    _ =𝔼[ X.filter_zero ] := sorry
        

example {a b : ℝ≥0} : a * b ≠ 0 → a ≠ 0 := fun a_1 ↦ left_ne_zero_of_mul a_1

example {α : Type} {A : Finset α} {f : α → ℝ} {g : α → ℝ}: 
  ∑ a ∈ A, (f a + g a) = ∑ a ∈ A, f a + ∑ a ∈ A, g a := Finset.sum_add_distrib

theorem exp_add_rv : 𝔼[X + Z] = 𝔼[X] + 𝔼[Z] := sorry
  --by simp_all![Finset.sum_add_distrib, Finset.sum_product, Finset.mul_sum]

theorem exp_const {c:ℝ} : 𝔼[ (c : Finrv P ℝ) ] = c := sorry

theorem exp_add_const {c:ℝ}: 𝔼[ (c : Finrv P ℝ) + X] = c + 𝔼[X] := 
                     by simp only [exp_add_rv, exp_const]

theorem exp_cnd_rv_add_const {c : ℝ}  : 
        ∀ ω ∈ P.Ω, (𝔼[ (c : Finrv P ℝ) + X |ᵥ Y]).val ω = c + (𝔼[X |ᵥ Y]).val ω := sorry

theorem exp_monotone (ge : ∀ω ∈ P.Ω, ∀ω ∈ P.Ω, P.prob.p ω > 0 → X.val ω ≥ Z.val ω) : 
        𝔼[X] ≥ 𝔼[Z] := sorry


/-- Expectations of identical rv are the same -/
theorem exp_congr (rv_same : ∀ω ∈ P.Ω, P.supp ω → X.val ω = Z.val ω) : 𝔼[X] = 𝔼[Z] := 
        calc 
           𝔼[X] = 𝔼[X.filter_zero] := sorry
           _ = 𝔼[Z.filter_zero]:= sorry 
             --Finset.sum_congr rfl fun ω inΩ ↦ congrArg (HMul.hMul (P.p ω)) (rv_same ω inΩ)
           _ = 𝔼[Z] := sorry

end BasicProperties

/- --------- Laws of the unconscious statistician ----------/

section Unconscious

variable (X : Finrv P ℝ) (B : Finrv P Bool) (C : Finrv P Bool) (Y : Finrv P V)

/-- Law of the unconscious statistician -/
theorem exp_sum_val :
        𝔼[ X ] = ∑ x ∈ (P.Ω.image X.val), ℙ[ X ᵣ== x ] * x := sorry

/-- Law of the unconscious statistician, conditional -/
theorem exp_sum_val_cnd :
        𝔼[ X | B ] = ∑ x ∈ (P.Ω.image X.val), ℙ[ X ᵣ== x | B ] * x := sorry

/-- Law of the unconscious statistician, conditional random variable -/
theorem exp_sum_val_cnd_rv  :
  ∀ ω ∈ P.Ω, (𝔼[X |ᵥ Y ]).val ω = ∑ y ∈ V, ℙ[Y ᵣ== (Y.val ω)] * 𝔼[X | Y ᵣ== (Y.val ω)]  :=
    sorry

end Unconscious

/- ------------ Law of total expectation ----------/

section Total

variable (X : Finrv P ℝ) (B : Finrv P Bool) (C : Finrv P Bool) (Y : Finrv P V)

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

/-- Constructs a probability space as a product of a probability 
space and a dependent probability space. -/
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


/- Old ρ related functions

/-- Needed to handle a multiplication with 0 -/
class HMulZero (G : Type) extends HMul ℝ≥0 G G, Zero G, AddZeroClass G where
  zero_mul : (a : G) → (0:ℝ≥0) * a = (0:G) 

instance instHMulZeroReal : HMulZero ℝ where
  hMul := fun a b => ↑a * b
  zero_mul := zero_mul
  zero := 0
  
  
instance instHMulZeroRealPlus : HMulZero ℝ≥0 where
  hMul := fun a b => a * b
  zero_mul := zero_mul
  zero := 0

-- This is the random variable output type
variable {ρ : Type} [HMulZero ρ] [AddCommMonoid ρ] 


section RhoManipulation

theorem mul_eq_zero_of_left_eq_zero {a : ℝ≥0} {b: ρ} : a = 0 → a * b = 0 := 
  fun h => by simp_all only [HMulZero.zero_mul]

theorem leftrho_ne_of_ne_zero_mul {a : ℝ≥0} {b: ρ} : a * b ≠ 0 → a ≠ 0 := 
  fun h => mt mul_eq_zero_of_left_eq_zero h 

end RhoManipulation

--/
