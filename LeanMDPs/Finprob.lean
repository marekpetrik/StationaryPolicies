import Mathlib.Data.Nat.Basic
import Mathlib.Data.Real.Basic 
import Mathlib.Data.NNReal.Basic

import Mathlib.Data.Finset.Image
import Mathlib.Logic.Function.Defs 

import Mathlib.Data.Finsupp.Indicator


variable {τ : Type} 

open NNReal

---------- LSimplex Definitions  -----------------------------------------

section LSimplex

/-- states that p is a valid probability value -/
abbrev Prob (p : ℚ) : Prop := 0 ≤ p ∧ p ≤ 1

variable {p : ℚ}

theorem Prob.of_complement (h1 : Prob p) : Prob (1-p) := by aesop

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
theorem LSimplex.nonempty (h : LSimplex L) : L ≠ [] := 
        fun a => by have := h.normalized; simp_all 
        
abbrev LSimplex.npt : LSimplex L → L ≠ [] := LSimplex.nonempty

/-- all probability in the head element -/
def LSimplex.degenerate (h : LSimplex L) : Bool := L.head h.nonempty = 1


theorem LSimplex.mem_prob (h1 : LSimplex L) : ∀ p ∈ L, Prob p := 
  fun p a => ⟨ h1.nneg p a, 
               h1.normalized ▸ List.single_le_sum h1.nneg p a⟩
  
theorem LSimplex.degenerate_head_lt (S : LSimplex L) (nond : ¬S.degenerate) : L.head S.npt < 1 :=
    by have prob := LSimplex.mem_prob S (L.head S.npt) (List.head_mem (LSimplex.npt S))
       simp [LSimplex.degenerate] at nond              
       simp [Prob] at prob             
       exact lt_of_le_of_ne prob.2 nond

theorem List.scale_sum : (L.scale c).sum = c * L.sum := 
  by induction L
     · simp [List.scale]
     · simp_all [List.scale]
       ring

theorem List.scale_length : (L.scale c).length = L.length := by simp [List.scale]

theorem List.scale_nneg_of_nneg (h : ∀l ∈ L, 0 ≤ l) (h1 : 0 ≤ c) : (∀l ∈ L.scale c, 0 ≤ l) := 
  by induction L 
     · simp [List.scale]
     · simp_all [List.scale]
       exact Left.mul_nonneg h.1 h1
  
theorem List.append_nneg_of_nneg (h : ∀l ∈ L, 0 ≤ l) (h1 : 0 ≤ p) : (∀l ∈ p::L, 0 ≤ l) := 
  by aesop

/-- adds a new probability to a list and renormalizes the rest --/
def List.spread (L : List ℚ) (p : ℚ) : List ℚ := p :: (L.scale (1-p)) 
    
theorem List.spread_sum : (L.spread p).sum = L.sum * (1-p) + p := 
  by induction L
     · simp [List.spread, List.scale]
     · simp [List.spread, List.scale_sum]
       ring

theorem List.spread_ge0 (h1 : ∀l ∈ L, 0 ≤ l)  (h2 : Prob p) :  ∀ l ∈ (L.spread p), 0 ≤ l := 
    by simp [List.spread]
       constructor
       · exact h2.1
       · intro l a
         exact List.scale_nneg_of_nneg (L := L) (c := (1-p)) 
                                       h1 (Prob.of_complement h2).1 l a

-- spreads the simples to also incude the rpbability p
theorem LSimplex.spread (S : LSimplex L) (p : ℚ) (prob : Prob p) : LSimplex (L.spread p) :=
  {nneg := List.spread_ge0 S.nneg prob,
   normalized := by simp [List.spread_sum, S.normalized]}

/-- Removes head and rescales -/
def List.unspread : List ℚ → List ℚ
    | nil => nil
    | head :: tail => tail.scale (1-head)⁻¹
    
theorem List.unspread_length : L.unspread.length = L.tail.length := 
  by cases L; simp [List.unspread]; simp[List.unspread, List.scale]
    
theorem List.unspread_sum (npt: L ≠ []) (h : L.head npt < 1) : 
        (L.unspread).sum = (L.tail).sum / (1 - L.head npt)  := 
        by cases L; contradiction; simp_all [List.unspread, List.scale_sum]; ring

theorem List.unspread_ge0 (h1 : ∀l ∈ L, Prob l) : ∀l ∈ (L.unspread), 0 ≤ l := 
    by simp [List.unspread]
       cases L with
       | nil => simp_all only [List.not_mem_nil, IsEmpty.forall_iff, implies_true]
       | cons head tail => 
           simp_all [Prob.complement_inv_nneg]
           have hh : 0 ≤ (1-head)⁻¹ := Prob.complement_inv_nneg h1.1
           exact List.scale_nneg_of_nneg (L:=tail) (c:=(1-head)⁻¹) (fun l a ↦ (h1.2 l a).1) hh 
         
variable {L : List ℚ}

lemma false_of_p_comp1_zero_p_less_one (h1 : 1 - p = 0) (h2 : p < 1) : False := by linarith

theorem List.spread_of_unspread 
        (npt : L ≠ [])  (le1 : L.head npt < 1) : L = (L.unspread).spread (L.head npt) := 
   by induction L with 
      | nil => have := npt rfl; contradiction
      | cons head tail => 
             let h : (1-head) ≠ 0 := fun a => false_of_p_comp1_zero_p_less_one a le1
             simp_all [List.spread, List.unspread, List.scale]
  
theorem LSimplex.tail_sum (S : LSimplex L) : L.tail.sum = (1 - L.head S.npt) := 
  by cases L; have := S.npt; contradiction; have := S.normalized; simp at this ⊢; linarith

theorem LSimplex.unspread (S : LSimplex L) (h : ¬ S.degenerate) : LSimplex (L.unspread) :=
  {nneg := List.unspread_ge0 (LSimplex.mem_prob S),
   normalized := 
     by have npt := S.npt
        have hh := LSimplex.degenerate_head_lt S h
        have hh1 := S.tail_sum 
        have hh2 : (1 - L.head npt) ≠ 0 := by linarith
        rw[List.unspread_sum S.npt hh]
        exact (div_eq_one_iff_eq hh2).mpr hh1}
        
end LSimplex


-----------------   Section FinDist ----------------------------------------------------
section FinDist

/-- Finite probability distribution on a set-like list (non-duplicates) -/
structure Findist (Ω : List τ) : Type where
  pr : List ℚ                      -- probability measure 
  simplex : LSimplex pr            -- proof of a measure
  unique : Ω.Nodup                 -- Ω are unique
  lmatch : pr.length = Ω.length    -- lengths are the same
  
abbrev Delta : List τ → Type := Findist
abbrev Δ : List τ → Type := Delta

variable {Ω : List τ}
variable (F : Findist Ω) 

/-- add a new head -/
def Findist.spread (p : ℚ) (prob : Prob p) (ω : τ) (notin : ω ∉ Ω) : Findist (ω :: Ω) :=
    let pr' := F.pr.spread p
    {pr := pr', 
     simplex := F.simplex.spread p prob, 
     unique := by simp_all [F.unique],
     lmatch := by simp [pr', List.spread, List.scale_length, F.lmatch]}

/-- if nondegenenrate then construct a tail distribution -/
def Findist.unspread (h : ¬ F.simplex.degenerate): Findist (Ω.tail) :=
    let pr' := F.pr.unspread 
    let hl : pr'.length = F.pr.length - 1 := 
        by rw [List.unspread_length (L:=F.pr)]; exact List.length_tail F.pr
    {pr := pr',
     simplex := F.simplex.unspread h 
     unique := by have := F.unique; cases Ω; simp; simp_all
     lmatch := by simp [hl, F.lmatch]
    }

def Findist.singleton (t : τ) : Findist [t] := 
  {pr := [1], 
   simplex := LSimplex.singleton
   unique := List.nodup_singleton t,
   lmatch := by simp_all only [List.length_cons, List.length_nil, zero_add]}

theorem Findist.npt_Ω (F : Findist Ω) : Ω ≠ [] :=
  by have := F.lmatch
     have := F.simplex.npt  
     intro a; simp_all 

theorem Findist.head_notin (F : Findist Ω) : Ω.head F.npt_Ω ∉ Ω.tail := 
  by have := F.npt_Ω
     cases Ω
     · contradiction
     · exact List.Nodup.not_mem F.unique
     
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

def Finprob.spread (p : ℚ) (prob : Prob p) (ω : τ) (notin : ω ∉ P.Ω) : Finprob τ :=
  ⟨ω :: P.Ω, P.prob.spread p prob ω notin⟩
  
/-- all probability in the head -/
abbrev Finprob.degenerate (P : Finprob τ) : Bool := P.prob.simplex.degenerate

def Finprob.unspread (notd : ¬P.degenerate) : Finprob τ := 
  { Ω := P.Ω.tail, prob := P.prob.unspread notd}
    
def Finprob.length := P.Ω.length 

-- Define an induction principle for probability spaces
-- similar to the induction on lists, but also must argue about probability distributions

theorem Finprob.nonempty (F : Finprob τ) : ¬F.Ω.isEmpty := 
  by have := LSimplex.nonempty F.prob.simplex; have := F.prob.lmatch
     intro a; simp_all only [ne_eq, List.isEmpty_iff, List.length_nil, List.length_eq_zero_iff]

theorem Finprob.nonempty1 (F : Finprob τ) : F.Ω ≠ [] := fun eq => F.nonempty (eq ▸ List.isEmpty_nil)

theorem Finprob.nonempty2 (F : Finprob τ) : F.prob.pr ≠ [] := F.prob.simplex.nonempty
          
def Finprob.ωhead (P : Finprob τ) := P.Ω.head P.nonempty1

def Finprob.phead (P : Finprob τ) := P.prob.pr.head P.nonempty2

theorem Finprob.ωhead_notin_tail: P.ωhead ∉ P.Ω.tail := Findist.head_notin P.prob

theorem Finprob.phead_inpr : P.phead ∈ P.prob.pr := List.head_mem P.nonempty2
    
theorem Finprob.phead_prob : (Prob P.phead) := 
  P.prob.simplex.mem_prob P.phead P.phead_inpr

theorem Finprob.len_ge_one : 1 ≤ P.length := 
  by have := nonempty P; simp_all [Finprob.length]
     generalize P.Ω = L at this ⊢
     cases L; simp_all; simp_all

theorem Finprob.tail_tail (notd : ¬P.prob.simplex.degenerate) : (P.unspread notd).Ω = P.Ω.tail := 
  by simp_all only [Finprob.unspread]
        
lemma List.unique_head_notin_tail (L : List τ) (ne : L ≠ []) (nodup : L.Nodup) : L.head ne ∉ L.tail := by
  induction L
  · simp at ne 
  · simp [List.head, List.tail]
    simp_all only [ne_eq, reduceCtorEq, not_false_eq_true, List.nodup_cons]

theorem Finprob.head_notin_tail (P : Finprob τ) : (P.Ω.head (Finprob.nonempty1 P)) ∉ P.Ω.tail := by 
  have := P.prob.unique
  apply List.unique_head_notin_tail
  simp_all only [ne_eq]
 

theorem Finprob.unspread_shorter (notd : ¬P.prob.simplex.degenerate) : 
                                 (P.unspread notd).length = P.length - 1 :=
        by simp_all only [Finprob.unspread, Finprob.length, List.length_tail]
  
/-- Shows that spreading an unspread probability will create the same probability space -/ 
theorem Finprob.spread_of_unspread 
  {tail: Finprob τ} {p : ℚ} {ω : τ} { nongen : ¬P.degenerate } 
  (tail_h : tail = P.unspread nongen) (ph : P.phead = p) (ωh : P.ωhead = ω) 
    : P = (tail.spread p (ph ▸ P.phead_prob) ω (tail_h ▸ ωh ▸ P.ωhead_notin_tail)) := 
    by simp [Finprob.spread, Findist.spread]
       have := List.spread_of_unspread P.nonempty2
       sorry
       
------- Section Finprob Induction ----------------------------------------------------------

/-- induction principle for finite probabilities -/
def Finprob.elim.{u} {motive : Finprob τ → Sort u} 
        (degenerate :  (fp : Finprob τ) → (d : fp.degenerate) → motive fp)
        (composite : (tail : Finprob τ) → (ω : τ) → (notin : ω ∉ tail.Ω) → 
                (p : ℚ) → (inP : Prob p) → (motive tail) → motive (tail.spread p inP ω notin)) 
        (F : Finprob τ) : motive F := 
    if b1 : F.prob.pr = [] then
      by have := LSimplex.nonempty F.prob.simplex; simp_all
    else
      if b2 : F.degenerate then
        degenerate F b2
      else
        let tail := F.unspread b2
        let ω := F.ωhead 
        let p := F.phead
        let notin : ω ∉ tail.Ω := by 
            simp only [ω, tail, Finprob.unspread];  exact F.head_notin_tail
        let ih : motive tail := Finprob.elim  degenerate composite tail 
        let final := composite tail ω notin p (sorry) (ih)
        -- TODO: still needs to prove that tail.spread will reverse unspread    
        sorry
    termination_by F.length
    decreasing_by 
      simp [Finprob.unspread, Finprob.length]
      apply Finprob.len_ge_one

    
end Finprob

------------------------------ Section Finrv -----------------------------------

section Finrv

/-- Random variable defined on a finite probability space -/
structure Finrv (P : Finprob τ) (ρ : Type) : Type  where
  val : τ → ρ   -- actual value of the random variable

end Finrv
