import Mathlib.Data.Nat.Basic
import Mathlib.Data.Real.Basic 
import Mathlib.Data.Rat.Defs
import Mathlib.Data.NNReal.Basic

import Mathlib.Logic.Function.Defs 

import Mathlib.Data.Set.Basic 

import Mathlib.Data.Finset.Defs
import Mathlib.Data.Finset.Image

import Mathlib.Algebra.Group.Pi.Basic -- for Pi.single

variable {τ : Type} 

open NNReal

---------------------- Indicator -----------------

/-- Boolean indicator function -/
def indicator (cond : Bool) : ℚ := cond.rec 0 1
abbrev 𝕀 : Bool → ℚ := indicator

/-- Indicator is 0 or 1 -/
theorem ind_zero_one (cond : τ → Bool) (ω : τ) : 
  ((𝕀∘cond) ω = 1) ∨ ((𝕀∘cond) ω = 0) := 
    if h : (cond ω) then Or.inl (by simp only [Function.comp_apply, h, indicator])
    else Or.inr (by simp only [Function.comp_apply, h, indicator])

theorem ind_ge_zero (cond : τ → Bool) (ω : τ) : 0 ≤ (𝕀∘cond) ω :=  by
  by_cases (cond ω); simp_all [indicator]; simp_all [indicator]

---------- List Basic Properties Definitions  -----------------------------------------

section List

variable {L : List τ}

-- TODO: find the theorem in mathlib that does this 
theorem List.nonempty_length_gt_one (h : ¬L.isEmpty) : L.length ≥ 1 := 
    by simp_all
       cases L 
       · contradiction
       · exact tsub_add_cancel_iff_le.mp rfl

end List

---------- Probability Definitions  -----------------------------------------

section Probability

/-- states that p is a valid probability value -/
@[simp]
abbrev Prob (p : ℚ) : Prop := 0 ≤ p ∧ p ≤ 1

variable {p : ℚ}

@[simp]
theorem Prob.of_complement (h1 : Prob p) : Prob (1-p) := 
  by simp_all only [Prob, sub_nonneg, tsub_le_iff_right, le_add_iff_nonneg_right, and_self]

@[simp]
theorem Prob.complement_inv_nneg (h1 : Prob p) : 0 ≤ (1-p)⁻¹ := by simp_all only [Prob, inv_nonneg, sub_nonneg]


theorem Prob.lower_bound_fst (hp : Prob p)  {x y : ℚ}(h : x ≤ y) : x ≤ p * x + (1-p) * y := 
        have h2 : (1-p) * x ≤ (1-p) * y := mul_le_mul_of_nonneg_left h hp.of_complement.1
        calc 
          x = p * x + (1-p) * x := by ring
          _ ≤ p * x + (1-p) * y := by rel [h2]

theorem Prob.lower_bound_snd (hp : Prob p)  {x y : ℚ} (h : y ≤ x) : y ≤ p * x + (1-p) * y := 
        have h2 : p * y ≤ p * x := mul_le_mul_of_nonneg_left h hp.1
        calc 
          y = p * y + (1-p) * y := by ring
          _ ≤ p * x + (1-p) * y := by rel [h2]

theorem Prob.upper_bound_fst (hp : Prob p) {x y : ℚ} (h : y ≤ x) : p * x + (1-p) * y ≤ x :=
        have h2 : (1-p) * y ≤ (1-p) * x := mul_le_mul_of_nonneg_left h hp.of_complement.1
        calc 
          p * x + (1-p) * y ≤ p * x + (1-p) * x := by rel [h2]
          _ = x := by ring  

theorem Prob.upper_bound_snd (hp : Prob p) {x y : ℚ} (h : x ≤ y) : p * x + (1-p) * y ≤ y :=
        have h2 : p * x ≤ p * y := mul_le_mul_of_nonneg_left h hp.1
        calc 
          p * x + (1-p) * y ≤ p * y + (1-p) * y := by rel [h2]
          _ = y := by ring  
        

end Probability
---------- LSimplex Definitions  -----------------------------------------

section LSimplex

variable {p : ℚ}

def List.scale (L : List ℚ) (c : ℚ) : List ℚ := (L.map fun x↦x*c)

/-- Self-normalizing list of probabilities  --/
structure LSimplex (L : List ℚ) : Prop where
  nneg : ∀p ∈ L, 0 ≤ p               -- separate for convenience
  normalized : L.sum = 1             -- sums to 1
  
def LSimplex.singleton : LSimplex [1] := 
  ⟨fun p a => by simp_all only [List.mem_cons, List.not_mem_nil, or_false, zero_le_one], 
    List.sum_singleton⟩

variable {L : List ℚ}  {c : ℚ}
variable (S : LSimplex L)

/-- cannot define a simplex on an empty set -/
@[simp]
theorem LSimplex.nonempty (S : LSimplex L) : L ≠ [] := 
        fun a => by have := S.normalized; simp_all 
       
@[simp] 
abbrev LSimplex.npt : LSimplex L → L ≠ [] := LSimplex.nonempty

def LSimplex.phead (h : LSimplex L) : ℚ := L.head h.nonempty

/-- all probability in the head element -/
def LSimplex.degenerate (S : LSimplex L) : Bool := S.phead  == 1

@[reducible]
def LSimplex.supported  : Bool := ¬S.degenerate

@[simp]
theorem LSimplex.mem_prob (S : LSimplex L) : ∀ p ∈ L, Prob p := 
  fun p a => ⟨ S.nneg p a, 
               S.normalized ▸ List.single_le_sum S.nneg p a⟩
               
theorem LSimplex.phead_inpr  : S.phead ∈ L := List.head_mem S.nonempty

@[simp]
theorem LSimplex.phead_prob  : Prob S.phead := S.mem_prob S.phead S.phead_inpr
               
theorem LSimplex.phead_supp  (supp : S.supported) : S.phead  < 1 :=
  by simp [degenerate] at supp
     exact lt_of_le_of_ne S.phead_prob.2 supp 

theorem LSimplex.supported_head_lt_one  (supp : S.supported) : L.head S.npt < 1 :=
    by have prob := LSimplex.mem_prob S (L.head S.npt) (List.head_mem (LSimplex.npt S))
       simp [LSimplex.degenerate] at supp              
       simp [Prob] at prob             
       exact lt_of_le_of_ne prob.2 supp


@[simp]
theorem List.scale_sum : (L.scale c).sum = c * L.sum := 
  by induction L
     · simp [List.scale]
     · simp_all [List.scale]
       ring

@[simp]
theorem List.scale_length : (L.scale c).length = L.length := by simp [List.scale]

theorem List.scale_nneg_of_nneg (h : ∀l ∈ L, 0 ≤ l) (h1 : 0 ≤ c) : (∀l ∈ L.scale c, 0 ≤ l) := 
  by induction L 
     · simp [List.scale]
     · simp_all [List.scale]
       exact Left.mul_nonneg h.1 h1
  
theorem List.append_nneg_of_nneg (h : ∀l ∈ L, 0 ≤ l) (h1 : 0 ≤ p) : (∀l ∈ p::L, 0 ≤ l) := 
  by aesop

/-- adds a new probability to a list and renormalizes the rest --/
def List.grow (L : List ℚ) (p : ℚ) : List ℚ := p :: (L.scale (1-p)) 
    
theorem List.grow_sum : (L.grow p).sum = L.sum * (1-p) + p := 
  by induction L
     · simp [List.grow, List.scale]
     · simp [List.grow, List.scale_sum]
       ring

@[simp]
theorem List.grow_ge0 (h1 : ∀l ∈ L, 0 ≤ l)  (h2 : Prob p) :  ∀ l ∈ (L.grow p), 0 ≤ l := 
    by simp [List.grow]
       constructor
       · exact h2.1
       · intro l a
         exact List.scale_nneg_of_nneg 
               (L := L) (c := (1-p)) h1 (Prob.of_complement h2).1 l a

-- grows the simplex to also incude the probability p
@[simp]
theorem LSimplex.grow (S : LSimplex L) {p : ℚ} (prob : Prob p) : LSimplex (L.grow p) :=
  {nneg := List.grow_ge0 S.nneg prob,
   normalized := by simp [List.grow_sum, S.normalized]}

/-- Removes head and rescales -/
def List.shrink : List ℚ → List ℚ
    | nil => nil
    | head :: tail => tail.scale (1-head)⁻¹
    
@[simp]
theorem List.shrink_length : L.shrink.length = L.tail.length := 
  by cases L; simp [List.shrink]; simp[List.shrink, List.scale]

theorem List.shrink_length_less_one : L.shrink.length = L.length - 1 :=
    by simp only [shrink_length, length_tail]
       
    
@[simp]
theorem List.shrink_sum (npt: L ≠ []) (h : L.head npt < 1) : 
        (L.shrink).sum = (L.tail).sum / (1 - L.head npt)  := 
        by cases L; contradiction; simp_all [List.shrink, List.scale_sum]; ring

theorem List.shrink_ge0 (h1 : ∀l ∈ L, Prob l) : ∀l ∈ (L.shrink), 0 ≤ l := 
    by simp [List.shrink]
       cases L with
       | nil => simp_all only [List.not_mem_nil, IsEmpty.forall_iff, implies_true]
       | cons head tail => 
           simp_all only [mem_cons, Prob, forall_eq_or_imp]
           have hh : 0 ≤ (1-head)⁻¹ := Prob.complement_inv_nneg h1.1
           exact List.scale_nneg_of_nneg (L:=tail) (c:=(1-head)⁻¹) (fun l a ↦ (h1.2 l a).1) hh 

lemma false_of_p_comp1_zero_p_less_one (h1 : 1 - p = 0) (h2 : p < 1) : False := by linarith
  
@[simp]
theorem LSimplex.tail_sum (S : LSimplex L) : L.tail.sum = (1 - L.head S.npt) := 
  by cases L; have := S.npt; contradiction; have := S.normalized; simp at this ⊢; linarith

theorem LSimplex.degenerate_tail_zero (degen : S.degenerate) : ∀ p ∈ L.tail, p = 0 :=
  by simp [LSimplex.degenerate, LSimplex.phead] at degen
     have ts := S.tail_sum
     rw [degen] at ts; simp at ts
     have nneg := fun p a ↦ S.nneg p (List.mem_of_mem_tail a)
     have lez := fun p a ↦ List.single_le_sum nneg p a
     rw [ts] at lez
     intro p a
     have hl := nneg p a
     have hu := lez p a
     linarith

theorem LSimplex.shrink (S : LSimplex L) (supp : S.supported) : LSimplex (L.shrink) :=
  {nneg := List.shrink_ge0 (LSimplex.mem_prob S),
   normalized := 
     by have npt := S.npt
        have hh := LSimplex.supported_head_lt_one S supp
        have hh1 := S.tail_sum 
        have hh2 : (1 - L.head npt) ≠ 0 := by linarith
        rw[List.shrink_sum S.npt hh]
        exact (div_eq_one_iff_eq hh2).mpr hh1}
        
theorem List.grow_of_shrink 
        (S : LSimplex L) (supp : S.supported) : L = (L.shrink).grow (S.phead) := 
   by induction L with
      | nil => have := S.nonempty; contradiction 
      | cons head tail => 
             let h : (1-head) ≠ 0 := 
               fun a => false_of_p_comp1_zero_p_less_one a (S.phead_supp supp)
             simp_all [List.grow, List.shrink, List.scale, LSimplex.phead]

-- all props of the same type are equal
theorem LSimplex.grow_of_shrink (S : LSimplex L) (supp : S.supported) : 
        S = (List.grow_of_shrink S supp) ▸ (S.shrink supp).grow S.phead_prob := rfl
             
end LSimplex

---------------- FinDist ----------------------------------------------------

section FinDist

-- TODO: Is Findist even adding any value here?
/-- Finite probability distribution on a set-like list (non-duplicates) -/
structure Findist (N : ℕ)  : Type where
  ℙ : List ℚ                      -- probabilities
  simplex : LSimplex ℙ            -- proof of a measure
  lmatch : ℙ.length = N           -- correct length of probability
  
abbrev Delta : ℕ → Type := Findist
abbrev Δ : ℕ → Type := Delta

variable {N : ℕ} (F : Findist N) 

abbrev Findist.degenerate : Bool := F.simplex.degenerate
abbrev Findist.supported : Bool := F.simplex.supported

theorem Findist.supp_not_degen (supp : F.supported) : ¬ F.degenerate :=         
        by simp_all [supported, degenerate]
 
@[simp]
theorem Findist.nonempty (F : Findist N) : N ≥ 1 :=
  F.lmatch ▸ List.length_pos_iff.mpr F.simplex.npt 

@[simp]
theorem Findist.nonempty_P : F.ℙ ≠ [] :=
  by have := F.simplex.npt
     intro a; contradiction


/-- add a new head -/
def Findist.grow {p : ℚ} (prob : Prob p) : Findist (N + 1)  :=
    {ℙ       := F.ℙ.grow p,
     simplex := F.simplex.grow prob, 
     lmatch  := by simp [List.grow, List.scale_length, F.lmatch]}

/-- if nondegenenrate then construct a tail distribution -/
def Findist.shrink  (supp : F.supported) : Findist (N - 1)  :=
    -- see: https://lean-lang.org/theorem_proving_in_lean4/The-Conversion-Tactic-Mode/
    let hh :  F.ℙ.shrink.length = N - 1 := 
      calc 
        F.ℙ.shrink.length = F.ℙ.length - 1 := List.shrink_length_less_one 
        _ = N - 1 := by conv => lhs; rw [F.lmatch]
    {ℙ := F.ℙ.shrink
     simplex := F.simplex.shrink supp 
     lmatch := hh} --List.shrink_length_less_one (Findist.nonempty_P F)}


def Findist.singleton : Findist 1 := 
    {ℙ := [1] 
     simplex := LSimplex.singleton,
     lmatch := by simp_all only [List.length_cons, List.length_nil, zero_add]}

          
abbrev Findist.phead := F.simplex.phead 

--example (a : Prop) (b : Prop) : ¬(a ∧ b) = (¬ a) ∨ (¬b) := 

@[simp]
theorem Findist.phead_inpr : F.phead ∈ F.ℙ := List.head_mem F.nonempty_P

@[simp]
theorem Findist.phead_prob : Prob F.phead := F.simplex.mem_prob F.phead F.phead_inpr

theorem Findist.nondegenerate_head (supp : F.supported) : F.phead < 1 := 
  by have h1 := Findist.phead_prob F
     simp_all only [supported, LSimplex.supported, LSimplex.degenerate, 
                    LSimplex.phead, beq_iff_eq, phead, gt_iff_lt]
     simp! only [decide_not, Bool.not_eq_eq_eq_not, not, decide_eq_false_iff_not] at supp
     simp [Prob] at h1
     exact lt_of_le_of_ne h1.2 supp


-- For the use of ▸ see: https://proofassistants.stackexchange.com/questions/1380/how-do-i-convince-the-lean-4-type-checker-that-addition-is-commutative

theorem Findist.grow_shrink_type (_ : F.supported) : Findist (N - 1 + 1) = Findist N := 
        (Nat.sub_add_cancel F.nonempty) ▸ rfl

def Findist.growshrink (supp : F.supported) : Findist (N-1+1) := 
   (F.shrink supp).grow F.phead_prob  

-- TODO: can we incorporate this example in the theorem below?
example (supp : F.supported) : ((F.shrink supp).grow F.phead_prob).ℙ = F.ℙ :=
    by have h1 : F.supported := by simp_all only 
       simp [Findist.shrink, Findist.grow, Findist.phead]
       rw [←List.grow_of_shrink F.simplex h1] 
         

theorem Findist.grow_of_shrink_2 (supp : F.supported) : 
  F.growshrink supp = ((F.grow_shrink_type supp).mpr F) :=
    by have h1 : F.supported := by simp_all only  
       simp [Findist.growshrink, Findist.shrink, Findist.grow, Findist.phead]
       rw [Findist.mk.injEq]
       rw [←List.grow_of_shrink F.simplex h1] 
       congr; --TODO: here to deal with casts; need to understand them better (see example below)
         symm; exact Nat.sub_add_cancel F.nonempty;
         simp_all only [heq_cast_iff_heq, heq_eq_eq]
         
-- the induction principle is a pain in this way because of all the casts
       
------- Section Findist Induction ----------------------------------------------------------

-- TODO: induction for Findist?       

end FinDist

section UnderstandingCasts

universe u
example {α : Sort u} {a a' : α} (h : HEq a a') : Eq a a' :=
  let f (α β : Sort u) (a : α) (b : β) (h₁ : a ≍ b) : (ht : α = β) → (ht.mp a) = b := 
    h₁.rec (fun _ => rfl)
  f α α a a' h rfl
end UnderstandingCasts

-------------------------- Section Finprob ------------------------------------------------------
section Finprob

/-- Finite probability space. See Finsample for the definition of the sample space. -/
structure Finprob : Type where
  ℙ : List ℚ
  prob : LSimplex ℙ
  
variable (P : Finprob)

@[simp]
def Finprob.length := P.ℙ.length 
  

def Finprob.singleton : Finprob := 
   ⟨ [1], LSimplex.singleton ⟩

def Finprob.grow {p : ℚ} (prob : Prob p) : Finprob :=
  ⟨P.ℙ.grow p, P.prob.grow prob⟩
  
/-- all probability in the head -/
abbrev Finprob.degenerate  : Bool := P.prob.degenerate
abbrev Finprob.supported  : Bool := P.prob.supported

theorem Finprob.not_degen_supp (supp : ¬P.degenerate) : P.supported := 
  by simp_all [Finprob.degenerate, Finprob.supported] 

theorem Finprob.degen_of_not_supp (notsupp : ¬P.supported) : P.degenerate := 
  by simp_all [Finprob.degenerate, Finprob.supported] 

def Finprob.shrink (supp : P.supported) : Finprob := 
  {ℙ := P.ℙ.shrink, prob := P.prob.shrink supp}
    

-- Define an induction principle for probability spaces
-- similar to the induction on lists, but also must argue about probability distributions

theorem Finprob.nonempty : ¬P.ℙ.isEmpty := 
  by intro a; 
     simp_all only [LSimplex.nonempty P.prob, List.isEmpty_iff]

theorem Finprob.length_gt_zero : P.length ≥ 1 := 
    by simp [Finprob.length]
       exact List.nonempty_length_gt_one (P.nonempty)

theorem Finprob.shrink_length (supp : P.supported) : (P.shrink supp).length = P.length - 1 := 
    by  have h := Finprob.nonempty P
        simp [List.isEmpty] at h
        simp! [Finprob.shrink, Finprob.length, List.shrink, LSimplex.shrink]
       
theorem Finprob.shrink_length_lt (supp : P.supported) : (P.shrink supp).length < P.length := 
    by rw [Finprob.shrink_length P supp]
       exact Nat.sub_one_lt_of_lt (Finprob.length_gt_zero P)

theorem Finprob.nonempty_P : P.ℙ ≠ [] := P.prob.nonempty
          
@[simp]
def Finprob.phead := P.ℙ.head P.nonempty_P

@[simp]
def Finprob.ωhead := P.length - 1

theorem Finprob.phead_inpr : P.phead ∈ P.ℙ := List.head_mem P.nonempty_P
    
theorem Finprob.phead_prob : Prob P.phead := 
  P.prob.mem_prob P.phead P.phead_inpr

theorem Finprob.phead_supp_ne_one (supp : P.supported) : P.phead ≠ 1 := 
        by simp [Finprob.supported, LSimplex.supported, LSimplex.degenerate, LSimplex.phead] at supp
           simp [Finprob.phead]
           exact supp

theorem Finprob.len_ge_one : P.length ≥ 1 :=
  by simp [Finprob.length]
     have h := P.prob.nonempty
     have : P.ℙ.length ≠ 0 := by simp_all only [ne_eq, List.length_eq_zero_iff, not_false_eq_true]
     exact Nat.one_le_iff_ne_zero.mpr this

lemma List.unique_head_notin_tail (L : List τ) (ne : L ≠ []) (nodup : L.Nodup) : 
      L.head ne ∉ L.tail := 
  by induction L
     · simp at ne 
     · simp [List.head, List.tail]
       simp_all only [ne_eq, reduceCtorEq, not_false_eq_true, List.nodup_cons]

theorem Finprob.shrink_shorter (supp : P.supported) : 
                                 (P.shrink supp).length = P.length - 1 :=
        by simp_all only [length, shrink, List.shrink_length, List.length_tail]

/-- Shows that growing an shrink probability will create the same probability space -/ 
theorem Finprob.grow_of_shrink (supp : P.supported) : P = (P.shrink supp).grow P.phead_prob := 
    by rw [Finprob.mk.injEq] -- same fields equivalent to same structures
       simp [Finprob.shrink, Finprob.grow]
       apply List.grow_of_shrink
       simp_all only [decide_not, Bool.decide_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true,
                Bool.false_eq_true, decide_false, Bool.not_false]
       exact P.prob
       
------- Section Finprob Induction ----------------------------------------------------------

/-- induction principle for finite probabilities. Works as "induction P" -/
@[induction_eliminator]
def Finprob.induction {motive : Finprob → Prop} 
        (degenerate :  {fp : Finprob} → (d : fp.degenerate) → motive fp)
        (composite : (tail : Finprob) →  {p : ℚ} → (inP : Prob p) → 
                     (motive tail) → motive (tail.grow inP)) 
        (P : Finprob) : motive P := 
    if b1 : P.ℙ = [] then
      by have := LSimplex.nonempty P.prob; simp_all
    else
      if b2 : P.degenerate then
        degenerate b2
      else
        let indhyp := Finprob.induction  degenerate composite (P.shrink (P.not_degen_supp b2))
        (Finprob.grow_of_shrink P (P.not_degen_supp b2)) ▸ 
          composite (P.shrink (P.not_degen_supp b2)) P.phead_prob indhyp
    termination_by P.length
    decreasing_by 
      simp only [length, shrink, gt_iff_lt]
      exact Finprob.shrink_length_lt P (P.not_degen_supp b2)

end Finprob

------------------------------ Section Finrv -----------------------------------
section RandomVariable

/-- Random variable defined on a finite probability space (bijection to ℕ) -/

def FinRV (ρ : Type) := ℕ → ρ

-- operation

@[simp]
def FinRV.and (B : FinRV Bool) (C : FinRV Bool) : FinRV Bool :=
    fun ω ↦ B ω && C ω

infix:35 " ∧ᵣ " => FinRV.and

@[simp]
def FinRV.or (B : FinRV Bool) (C : FinRV Bool) : FinRV Bool :=
    fun ω ↦ B ω || C ω

infix:30 " ∨ᵣ " => FinRV.or

@[simp]
def FinRV.not (B : FinRV Bool) : FinRV Bool :=
  fun ω ↦ (B ω).not

prefix:40 "¬ᵣ" => FinRV.not


@[simp] 
def FinRV.eq {η : Type} [DecidableEq η] (Y : FinRV η) (y : η) : FinRV Bool := 
  (fun ω ↦ decide (Y ω = y) )

infix:50 "=ᵣ" => FinRV.eq

@[simp]
def FinRV.leq {η : Type} [LE η] [DecidableLE η] (Y : FinRV η) (y : η) : FinRV Bool := 
  (fun ω ↦ Y ω ≤ y)

infix:50 "≤ᵣ" => FinRV.leq

/-- Shows equivalence when extending the random variable to another element. -/
theorem FinRV.le_of_le_eq (D : FinRV ℕ) (n : ℕ) : ((D ≤ᵣ n) ∨ᵣ (D =ᵣ n.succ)) = (D ≤ᵣ n.succ) := by 
  funext x --extensionality principle for functions
  unfold FinRV.leq FinRV.eq FinRV.or
  grind only [cases Or]



end RandomVariable

------------------------------ Section Probability ---------------------------

section Probability

----- standard probability

/-- Probability of a random variable. Does not enforce normalization -/
def List.iprodb (ℙ : List ℚ) (B : FinRV Bool) : ℚ :=
    match ℙ with
    | [] => 0
    | head :: tail =>  (B tail.length).rec 0 head + tail.iprodb B
    

variable (P : Finprob) (B : FinRV Bool) (C : FinRV Bool)

variable (L : List ℚ)

theorem List.scale_innerprod  (x : ℚ) : (L.scale x).iprodb B = x * (L.iprodb B) := 
  by induction L with
     | nil => simp_all [List.scale, List.iprodb]
     | cons head tail =>
            simp_all [List.iprodb, List.scale]
            cases B tail.length
            · simp_all
            · simp_all
              ring
            
theorem List.decompose_supp (h : L ≠ []) (ne1 : L.head h ≠ 1): 
    L.iprodb B = (B (L.length - 1)).rec 0 (L.head h) + (1-L.head h) * (L.shrink.iprodb B)  :=
    by conv => lhs; unfold iprodb
       cases L with
       | nil => simp at h
       | cons head tail => 
        simp [List.shrink]
        have := tail.scale_innerprod B (1-head)⁻¹
        simp_all
        have hnz : 1 - head ≠ 0 := 
          by by_contra; have : head = 1 := by linarith; 
             contradiction
        calc 
          tail.iprodb B = 1 * tail.iprodb B := by ring
          _ = (1 - head) * (1 - head)⁻¹ * tail.iprodb B  := 
              by rw [Rat.mul_inv_cancel (1-head) hnz]
          _ = (1 - head) * ((1 - head)⁻¹ * tail.iprodb B ) := by ring

theorem List.iprod_eq_zero_of_zeros  (hz : ∀ p ∈ L, p = 0) : L.iprodb B = 0 :=
  by induction L with
     | nil => simp [iprodb]
     | cons head tail => simp_all [iprodb]; cases B tail.length; simp; simp


theorem List.iprod_first_of_tail_zero  (hn : L ≠ []) (hz : ∀ p ∈ L.tail, p = 0) :
   L.iprodb B = (B L.tail.length).rec 0 (L.head hn)  := 
   by unfold iprodb
      cases L
      · contradiction
      · simp; simp at hz; (expose_names; exact iprod_eq_zero_of_zeros B tail hz)

/-- Probability of B -/
def probability : ℚ :=  P.ℙ.iprodb B
    
notation "ℙ[" B "//" P "]" => probability P B 

--- main decomposition properties

/-- If supported then can be decomposed to the immediate probability and the 
remaining probability -/
theorem Finprob.decompose_supp (supp : P.supported) : 
    ℙ[ B // P ] = (B P.ωhead).rec 0 P.phead + (1-P.phead) * ℙ[ B // P.shrink supp ] := 
      by simp [Finprob.phead, Finprob.shrink]
         exact P.ℙ.decompose_supp B P.nonempty_P (P.phead_supp_ne_one supp)
     
theorem Finprob.decompose_degen (degen : P.degenerate) : ℙ[ B // P ] = (B P.ωhead).rec 0 P.phead  :=
  by have tz := P.prob.degenerate_tail_zero degen
     simp [probability, Finprob.ωhead]
     have almost := P.ℙ.iprod_first_of_tail_zero B P.nonempty_P tz 
     rw [List.length_tail] at almost
     exact almost 
       
--- basic properties

theorem Finprob.in_prob (P : Finprob) : Prob ℙ[ B // P ] := 
    by have hip := P.phead_prob
       by_cases h : P.supported
       · rw [P.decompose_supp B h]
         have ih := Finprob.in_prob (P.shrink h)
         simp only [Prob] at ⊢ ih hip
         cases B P.ωhead
         · simp only; 
           constructor; 
           . have prd_zero : 0 ≤ (1 - P.phead) * ℙ[B//P.shrink h] := Rat.mul_nonneg P.phead_prob.of_complement.1 ih.1
             simp_all only [phead, probability, zero_add]
           · have prd_one : (1 - P.phead) * ℙ[B//P.shrink h] ≤ 1 := mul_le_one₀ P.phead_prob.of_complement.2 ih.1 ih.2
             simp_all only [phead, probability, zero_add]
         · simp only; 
           constructor; 
           · calc
               0 ≤ ℙ[B//P.shrink h] := ih.1
               _ ≤ P.phead * 1 + (1 - P.phead) * ℙ[B//P.shrink h] := P.phead_prob.lower_bound_snd ih.2   
               _ = P.phead  + (1 - P.phead) * ℙ[B//P.shrink h] := by ring
           · calc 
               P.phead + (1 - P.phead) * ℙ[B//P.shrink h] = 
                P.phead * 1 + (1 - P.phead) * ℙ[B//P.shrink h] := by ring
               _ ≤ 1 := P.phead_prob.upper_bound_fst ih.2
       · rw [P.decompose_degen B (P.degen_of_not_supp h) ]
         cases B P.ωhead 
         · simp_all
         · simp_all   
    termination_by P.length
    decreasing_by exact shrink_length_lt P h

theorem Prob.ge_zero : ℙ[ B // P ] ≥ 0 := (P.in_prob B).left

theorem Prob.le_one : ℙ[ B // P ] ≤ 1 := (P.in_prob B).right


lemma List.iprodb_true_sum : L.iprodb (fun _ ↦ true) = L.sum := 
    by induction L
       · simp only  [iprodb, sum_nil]
       · simp_all only [iprodb, sum_cons]

theorem Prob.true_one : ℙ[ fun _ ↦ true // P] = 1 := 
    by simp only [probability]; rw [List.iprodb_true_sum]; exact P.prob.normalized

--- sums

theorem List.list_compl_sums_to_one (L : List ℚ) : L.iprodb B + L.iprodb (B.not) = L.sum :=
  by induction L with
     | nil => simp [List.iprodb]
     | cons head tail =>
        simp [List.iprodb]
        cases (B tail.length)
        · simp; linarith
        · simp; linarith

theorem Prob.prob_compl_sums_to_one : ℙ[B // P] + ℙ[¬ᵣB // P] = 1 :=
  calc 
    ℙ[ B // P ] + ℙ[ ¬ᵣB // P] = P.ℙ.sum := P.ℙ.list_compl_sums_to_one B
    _ = 1 := P.prob.normalized

theorem Prob.prob_compl_one_minus : ℙ[¬ᵣB // P] = 1 - ℙ[B // P] :=
    by have := Prob.prob_compl_sums_to_one P B
       linarith

theorem List.law_of_total_probs (L : List ℚ)  : L.iprodb B = L.iprodb (B ∧ᵣ C) + L.iprodb (B ∧ᵣ (¬ᵣC) ) := 
    by induction L with  
       | nil => simp [List.iprodb]
       | cons head tail => 
          simp [List.iprodb]
          cases bB: B tail.length
          · cases bC : C tail.length; simp_all; simp_all
          · cases bC : C tail.length
            · simp_all; ring;
            · simp_all; ring; 
          
theorem Prob.law_of_total_probs : ℙ[B // P] = ℙ[ B ∧ᵣ C // P] + ℙ[ B ∧ᵣ ¬ᵣC //P] := P.ℙ.law_of_total_probs B C

---- conditional probability 

/-- Conditional probability of B -/
def probability_cnd : ℚ := 
    ℙ[ B ∧ᵣ C // P ] / ℙ[ C // P ]

notation "ℙ[" B "|" C "//" P "]" => probability_cnd P B C

theorem Prob.conditional_total (h : 0 < ℙ[C // P]) : ℙ[B ∧ᵣ C // P] =  ℙ[ B | C // P] * ℙ[ C // P] :=
  by simp [probability_cnd] at ⊢ h 
     have : P.ℙ.iprodb C * (P.ℙ.iprodb C)⁻¹ = 1 := Rat.mul_inv_cancel (P.ℙ.iprodb C) (Ne.symm (ne_of_lt h))
     calc 
        P.ℙ.iprodb (B ∧ᵣC) = P.ℙ.iprodb (B ∧ᵣC) * 1 := by ring
        _ = P.ℙ.iprodb (B ∧ᵣC) * (P.ℙ.iprodb C * (P.ℙ.iprodb C)⁻¹) := by rw [←this]
        _ = P.ℙ.iprodb (B ∧ᵣ C) / P.ℙ.iprodb C * P.ℙ.iprodb C := by ring
     

theorem Prob.law_of_total_probs_cnd 
  (h1 : 0 < ℙ[C // P]) (h2 : ℙ[C // P] < 1)  : ℙ[B // P] = ℙ[B | C // P] * ℙ[ C // P] + ℙ[B | ¬ᵣC //P] * ℙ[¬ᵣC // P] :=
        by have h2' : 0 < ℙ[¬ᵣC // P] := by rw [prob_compl_one_minus]; linarith
           rw [←Prob.conditional_total P B C h1]
           rw [←Prob.conditional_total P B (¬ᵣC) h2']
           exact law_of_total_probs P B C

end Probability

section Expectations

def List.iprod (ℙ : List ℚ) (X : FinRV ℚ) : ℚ :=
    match ℙ with
    | [] => 0
    | head :: tail =>  head * (X tail.length) + tail.iprod X


variable (P : Finprob) (X Y Z: FinRV ℚ) (B : FinRV Bool)

def expect : ℚ := P.ℙ.iprod X

notation "𝔼[" X "//" P "]" => expect P X 

-- expectation for a joint probability space and random variable
notation "𝔼[" PX "]" => expect PX.1 PX.2



-- conditional expectation

def expect_cnd : ℚ := P.ℙ.iprod X / P.ℙ.iprodb B

notation "𝔼[" X "|" B "//" P "]" => expect_cnd P X B

-- expectation for a joint probability space and random variable
notation "𝔼[" PX "]" => expect PX.1 PX.2
notation "𝔼[" PX "|" B "]" => expect_cnd PX.1 PX.2 B

-- conditional expectation: conditioning on a random variable: this defintion creates a probability
-- space and a random variable

variable {K : ℕ} (D : FinRV (Fin K.succ))  -- a discrete random variable with K+1 values

end Expectations



-- The section defines measurabilty of random variables
section Measurability

/-- Represents the *generator* of the sample space of a Finprob. Each element
is mapped to a single generator. Note that different Finsample definitions
may induce equivalent sample spaces. Also there is no guarantee
that there will not be a generator with zero probability. -/
def Finprob.SampleMap (P : Finprob) (m : ℕ) : Type := Fin P.length → Fin m

variable {ρ : Type} {P : Finprob} {m : ℕ} 

instance : CoeOut (Finprob.SampleMap P m) (FinRV (Fin m)) where coe a := 
           (fun ω ↦ if h : ω < P.length then a ⟨ω, h⟩ else a ⟨0,P.len_ge_one⟩)
  
/-- Defines that the random variable X is measurable with respect to a map 
and a reduced random variable Y 
--/
def FinRV.MeasurableRV (X Y : FinRV ρ) (ℱ : P.SampleMap m) : Prop := ∀ ω : Fin P.length, X ω = Y (ℱ ω)

/-- Defines the aggregated probability in the compacted space --/
def FinProb.MeasurableProb {L : List ℚ} (ℱ : P.SampleMap L.length) : Prop := 
    ∀ m : Fin L.length, ℙ[ℱ =ᵣ m // P] = L.get m 
                         

--example {m : ℕ} {ℱ : P.SampleMap m} (h: X.Measurable Y ℱ) : 1 = 𝔼[ X // P ] := by sorry
end Measurability
