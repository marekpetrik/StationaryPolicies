import Mathlib.Data.Nat.Basic
import Mathlib.Data.Real.Basic 
import Mathlib.Data.NNReal.Basic

import Mathlib.Data.Finset.Image
import Mathlib.Logic.Function.Defs 

import Mathlib.Data.Finsupp.Indicator


variable {τ : Type} 

open NNReal

---------------------- Indicator -----------------

/-- Boolean indicator function -/
@[reducible] 
def indicator (cond : Bool) : ℝ := cond.rec 0 1
abbrev 𝕀 : Bool → ℝ := indicator

/-- Indicator is 0 or 1 -/
theorem ind_zero_one (cond : τ → Bool) (ω : τ) : 
  ((𝕀∘cond) ω = 1) ∨ ((𝕀∘cond) ω = 0) := 
    if h : (cond ω) then Or.inl (by simp only [Function.comp_apply, h, indicator])
    else Or.inr (by simp only [Function.comp_apply, h, indicator])

theorem ind_ge_zero (cond : τ → Bool) (ω : τ) : 0 ≤ (𝕀∘cond) ω :=  by
  by_cases (cond ω); simp_all [indicator]; simp_all [indicator]

---------- LSimplex Definitions  -----------------------------------------

section LSimplex

/-- states that p is a valid probability value -/
abbrev Prob (p : ℚ) : Prop := 0 ≤ p ∧ p ≤ 1

variable {p : ℚ}

@[simp]
theorem Prob.of_complement (h1 : Prob p) : Prob (1-p) := by aesop

@[simp]
theorem Prob.complement_inv_nneg (h1 : Prob p) : 0 ≤ (1-p)⁻¹ := by aesop

def List.scale (L : List ℚ) (c : ℚ) : List ℚ := (L.map fun x↦x*c)

/-- Self-normalizing list of probabilities  --/
structure LSimplex (L : List ℚ) : Prop where
  nneg : ∀p ∈ L, 0 ≤ p               -- separate for convenience
  normalized : L.sum = 1             -- sums to 1

def LSimplex.singleton : LSimplex [1] := 
  ⟨fun p a => by simp_all only [List.mem_cons, List.not_mem_nil, or_false, zero_le_one], 
    List.sum_singleton⟩

variable {L : List ℚ}  {c : ℚ}

/-- cannot define a simplex on an empty set -/
@[simp]
theorem LSimplex.nonempty (S : LSimplex L) : L ≠ [] := 
        fun a => by have := S.normalized; simp_all 
       
@[simp] 
abbrev LSimplex.npt : LSimplex L → L ≠ [] := LSimplex.nonempty

def LSimplex.phead (h : LSimplex L) : ℚ := L.head h.nonempty

/-- all probability in the head element -/
def LSimplex.degenerate (S : LSimplex L) : Bool := S.phead  == 1

@[simp]
theorem LSimplex.mem_prob (h1 : LSimplex L) : ∀ p ∈ L, Prob p := 
  fun p a => ⟨ h1.nneg p a, 
               h1.normalized ▸ List.single_le_sum h1.nneg p a⟩
               
theorem LSimplex.phead_inpr (S : LSimplex L) : S.phead ∈ L := List.head_mem S.nonempty

@[simp]
theorem LSimplex.phead_prob (S : LSimplex L) : Prob S.phead := S.mem_prob S.phead S.phead_inpr
               
theorem LSimplex.phead_nongen (S : LSimplex L) (nongen : ¬S.degenerate) : S.phead  < 1 :=
  by simp [degenerate] at nongen
     exact lt_of_le_of_ne S.phead_prob.2 nongen 

theorem LSimplex.degenerate_head_lt (S : LSimplex L) (nond : ¬S.degenerate) : L.head S.npt < 1 :=
    by have prob := LSimplex.mem_prob S (L.head S.npt) (List.head_mem (LSimplex.npt S))
       simp [LSimplex.degenerate] at nond              
       simp [Prob] at prob             
       exact lt_of_le_of_ne prob.2 nond

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
theorem LSimplex.grow (S : LSimplex L) (p : ℚ) (prob : Prob p) : LSimplex (L.grow p) :=
  {nneg := List.grow_ge0 S.nneg prob,
   normalized := by simp [List.grow_sum, S.normalized]}

/-- Removes head and rescales -/
def List.shrink : List ℚ → List ℚ
    | nil => nil
    | head :: tail => tail.scale (1-head)⁻¹
    
@[simp]
theorem List.shrink_length : L.shrink.length = L.tail.length := 
  by cases L; simp [List.shrink]; simp[List.shrink, List.scale]
    
@[simp]
theorem List.shrink_sum (npt: L ≠ []) (h : L.head npt < 1) : 
        (L.shrink).sum = (L.tail).sum / (1 - L.head npt)  := 
        by cases L; contradiction; simp_all [List.shrink, List.scale_sum]; ring

theorem List.shrink_ge0 (h1 : ∀l ∈ L, Prob l) : ∀l ∈ (L.shrink), 0 ≤ l := 
    by simp [List.shrink]
       cases L with
       | nil => simp_all only [List.not_mem_nil, IsEmpty.forall_iff, implies_true]
       | cons head tail => 
           simp_all [Prob.complement_inv_nneg]
           have hh : 0 ≤ (1-head)⁻¹ := Prob.complement_inv_nneg h1.1
           exact List.scale_nneg_of_nneg (L:=tail) (c:=(1-head)⁻¹) (fun l a ↦ (h1.2 l a).1) hh 
         
variable {L : List ℚ}

lemma false_of_p_comp1_zero_p_less_one (h1 : 1 - p = 0) (h2 : p < 1) : False := by linarith
  
@[simp]
theorem LSimplex.tail_sum (S : LSimplex L) : L.tail.sum = (1 - L.head S.npt) := 
  by cases L; have := S.npt; contradiction; have := S.normalized; simp at this ⊢; linarith

theorem LSimplex.shrink (S : LSimplex L) (h : ¬ S.degenerate) : LSimplex (L.shrink) :=
  {nneg := List.shrink_ge0 (LSimplex.mem_prob S),
   normalized := 
     by have npt := S.npt
        have hh := LSimplex.degenerate_head_lt S h
        have hh1 := S.tail_sum 
        have hh2 : (1 - L.head npt) ≠ 0 := by linarith
        rw[List.shrink_sum S.npt hh]
        exact (div_eq_one_iff_eq hh2).mpr hh1}
        
theorem LSimplex.grow_of_shrink 
        (S : LSimplex L)  (nongen : ¬ S.degenerate) : L = (L.shrink).grow (S.phead) := 
   by induction L with
      | nil => have := S.nonempty; contradiction 
      | cons head tail => 
             let h : (1-head) ≠ 0 := 
               fun a => false_of_p_comp1_zero_p_less_one a (S.phead_nongen nongen)
             simp_all [List.grow, List.shrink, List.scale, LSimplex.phead]
             
end LSimplex

-----------------   Section FinDist ----------------------------------------------------
section FinDist

/-- Finite probability distribution on a set-like list (non-duplicates) -/
structure Findist (Ω : List τ) (pr : List ℚ) : Type where
  simplex : LSimplex pr            -- proof of a measure
  unique : Ω.Nodup                 -- Ω are unique
  lmatch : pr.length = Ω.length    -- lengths are the same
  
abbrev Delta : List τ → List ℚ → Type := Findist
abbrev Δ : List τ → List ℚ → Type := Delta

variable {Ω : List τ} {pr : List ℚ}
variable (F : Findist Ω pr) 

abbrev Findist.degenerate : Bool := F.simplex.degenerate

/-- add a new head -/
def Findist.grow {p : ℚ} {ω : τ} (prob : Prob p)  (notin : ω ∉ Ω) : Findist (ω :: Ω) (pr.grow p) :=
    {simplex := F.simplex.grow p prob, 
     unique := by simp_all [F.unique],
     lmatch := by simp [pr', List.grow, List.scale_length, F.lmatch]}

/-- if nondegenenrate then construct a tail distribution -/
def Findist.shrink (h : ¬F.simplex.degenerate): Findist (Ω.tail) :=
    let pr' := F.pr.shrink 
    let hl : pr'.length = F.pr.length - 1 := 
        by rw [List.shrink_length (L:=F.pr)]; exact List.length_tail 
    {pr := pr',
     simplex := F.simplex.shrink h 
     unique := by have := F.unique; cases Ω; simp; simp_all
     lmatch := by simp [hl, F.lmatch]}

def Findist.singleton (t : τ) : Findist [t] := 
    { pr := [1], 
      simplex := LSimplex.singleton
      unique := List.nodup_singleton t,
      lmatch := by simp_all only [List.length_cons, List.length_nil, zero_add]}

@[simp]
theorem Findist.nonempty_Ω (F : Findist Ω) : Ω ≠ [] :=
  by have h1 := F.lmatch
     have h2 := F.simplex.npt  
     intro a; simp_all only [List.length_nil, List.length_eq_zero_iff]

@[simp]
theorem Findist.nonempty_P : F.pr ≠ [] :=
  by have := F.simplex.npt
     intro a; contradiction
          
abbrev Findist.ωhead := Ω.head F.nonempty_Ω

abbrev Findist.phead := F.pr.head F.nonempty_P

@[simp]
theorem Findist.phead_inpr : F.phead ∈ F.pr := List.head_mem F.nonempty_P

@[simp]
theorem Findist.phead_prob : Prob F.phead := F.simplex.mem_prob F.phead F.phead_inpr

theorem Findist.ωhead_notin_tail (F : Findist Ω) : Ω.head F.nonempty_Ω ∉ Ω.tail := 
  by have := F.nonempty_Ω
     cases Ω
     · contradiction
     · exact List.Nodup.notMem F.unique

theorem Findist.nondegenerate_head (nongen : ¬F.degenerate) : F.phead < 1 := 
  by have h1 := Findist.phead_prob F
     simp_all only [degenerate, LSimplex.degenerate, LSimplex.phead, beq_iff_eq, phead, gt_iff_lt]
     --unfold Prob at h1
     exact lt_of_le_of_ne h1.2 nongen

theorem Findist.Ω_eq_headtail (F : Findist Ω) : Ω = F.ωhead :: Ω.tail :=  
  by simp_all only [List.head_cons_tail]

-- For the use of ▸ see: https://proofassistants.stackexchange.com/questions/1380/how-do-i-convince-the-lean-4-type-checker-that-addition-is-commutative
      
theorem Findist.grow_of_shrink (nongen : ¬F.degenerate) : 
  F.Ω_eq_headtail ▸ (F.shrink nongen).grow F.phead_prob F.ωhead_notin_tail = F :=
    by let G := (F.shrink nongen).grow F.phead_prob F.ωhead_notin_tail
       have h1 : ¬ F.simplex.degenerate := by simp_all 
       have h2 : F.pr = G.pr
       simp_all [grow, List.grow]
       
       

end FinDist

-------------------------- Section Finprob ------------------------------------------------------
section Finprob

/-- Finite probability space -/
structure Finprob (τ : Type) : Type where
  Ω : List τ         
  prob : Findist Ω   

variable (P : Finprob τ)

def Finprob.singleton (ω : τ) : Finprob τ := 
   ⟨ [ω], Findist.singleton ω ⟩

def Finprob.grow {p : ℚ} {ω : τ} (prob : Prob p)  (notin : ω ∉ P.Ω) : Finprob τ :=
  ⟨ω :: P.Ω, P.prob.grow prob notin⟩
  
/-- all probability in the head -/
abbrev Finprob.degenerate (P : Finprob τ) : Bool := P.prob.simplex.degenerate

def Finprob.shrink (notd : ¬P.degenerate) : Finprob τ := 
  { Ω := P.Ω.tail, prob := P.prob.shrink notd}
    
def Finprob.length := P.Ω.length 

-- Define an induction principle for probability spaces
-- similar to the induction on lists, but also must argue about probability distributions

theorem Finprob.nonempty (F : Finprob τ) : ¬F.Ω.isEmpty := 
  by have := LSimplex.nonempty F.prob.simplex; have := F.prob.lmatch
     intro a; simp_all only [ne_eq, List.isEmpty_iff, List.length_nil, List.length_eq_zero_iff]

theorem Finprob.nonempty_Ω (F : Finprob τ) : F.Ω ≠ [] := fun eq => F.nonempty (eq ▸ List.isEmpty_nil)

theorem Finprob.nonempty_P (F : Finprob τ) : F.prob.pr ≠ [] := F.prob.simplex.nonempty
          
def Finprob.ωhead (P : Finprob τ) := P.Ω.head P.nonempty_Ω

def Finprob.phead (P : Finprob τ) := P.prob.pr.head P.nonempty_P

theorem Finprob.ωhead_notin_tail: P.ωhead ∉ P.Ω.tail := Findist.ωhead_notin_tail P.prob

theorem Finprob.phead_inpr : P.phead ∈ P.prob.pr := List.head_mem P.nonempty_P
    
theorem Finprob.phead_prob : (Prob P.phead) := 
  P.prob.simplex.mem_prob P.phead P.phead_inpr

theorem Finprob.len_ge_one : 1 ≤ P.length := 
  by have := nonempty P; simp_all [Finprob.length]
     generalize P.Ω = L at this ⊢
     cases L; simp_all; simp_all

theorem Finprob.tail_tail (notd : ¬P.prob.simplex.degenerate) : (P.shrink notd).Ω = P.Ω.tail := 
  by simp_all only [Finprob.shrink]
        
lemma List.unique_head_notin_tail (L : List τ) (ne : L ≠ []) (nodup : L.Nodup) : L.head ne ∉ L.tail := by
  induction L
  · simp at ne 
  · simp [List.head, List.tail]
    simp_all only [ne_eq, reduceCtorEq, not_false_eq_true, List.nodup_cons]

theorem Finprob.head_notin_tail (P : Finprob τ) : (P.Ω.head (Finprob.nonempty_Ω P)) ∉ P.Ω.tail := by 
  have := P.prob.unique
  apply List.unique_head_notin_tail
  simp_all only [ne_eq]
 

theorem Finprob.shrink_shorter (notd : ¬P.prob.simplex.degenerate) : 
                                 (P.shrink notd).length = P.length - 1 :=
        by simp_all only [Finprob.shrink, Finprob.length, List.length_tail]
  
/-- Shows that growing an shrink probability will create the same probability space -/ 
theorem Finprob.grow_of_shrink 
     (nongen : ¬P.degenerate) : 
     P = (P.shrink nongen).grow P.phead_prob P.ωhead_notin_tail := 
    by simp [Finprob.grow, Findist.grow]
       have peq := LSimplex.grow_of_shrink P.nonempty_P (sorry)
       sorry 
       
------- Section Finprob Induction ----------------------------------------------------------

/-- induction principle for finite probabilities -/
def Finprob.elim.{u} {motive : Finprob τ → Sort u} 
        (degenerate :  (fp : Finprob τ) → (d : fp.degenerate) → motive fp)
        (composite : (tail : Finprob τ) → (ω : τ) → (notin : ω ∉ tail.Ω) → 
                (p : ℚ) → (inP : Prob p) → (motive tail) → motive (tail.grow inP notin)) 
        (F : Finprob τ) : motive F := 
    if b1 : F.prob.pr = [] then
      by have := LSimplex.nonempty F.prob.simplex; simp_all
    else
      if b2 : F.degenerate then
        degenerate F b2
      else
        let tail := F.shrink b2
        let ω := F.ωhead 
        let p := F.phead
        let notin : ω ∉ tail.Ω := by 
            simp only [ω, tail, Finprob.shrink];  exact F.head_notin_tail
        let ih : motive tail := Finprob.elim  degenerate composite tail 
        let final := composite tail ω notin p (sorry) (ih)
        -- TODO: still needs to prove that tail.grow will reverse shrink    
        sorry
    termination_by F.length
    decreasing_by 
      simp [Finprob.shrink, Finprob.length]
      apply Finprob.len_ge_one
    
end Finprob

------------------------------ Section Finrv -----------------------------------

section Finrv

/-- Random variable defined on a finite probability space -/
structure Finrv (P : Finprob τ) (ρ : Type) : Type  where
  val : τ → ρ   -- actual value of the random variable

end Finrv
