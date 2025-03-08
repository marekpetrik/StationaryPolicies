import Mathlib.Data.Nat.Basic
import Mathlib.Data.Real.Basic 
import Mathlib.Data.NNReal.Basic

import Mathlib.Data.Finset.Image
import Mathlib.Logic.Function.Defs -- Function.Injective

import Mathlib.Data.Finsupp.Indicator

--import Mathlib.Topology.UnitInterval

--open unitInterval

--universe u

variable {τ : Type} 

open NNReal

section LSimplex

abbrev Prob (p : ℚ) : Prop := 0 ≤ p ∧ p ≤ 1

variable {p : ℚ}

theorem prob_of_complement (h1 : Prob p) : Prob (1-p) := by aesop

theorem prob_complement_inv_nneg (h1 : Prob p) : 0 ≤ (1-p)⁻¹ := by aesop

def List.scale (L : List ℚ) (c : ℚ) : List ℚ := (L.map fun x↦x*c)

/-- Self-normalizing list of probabilities --/
structure LSimplex (L : List ℚ) : Prop where
  nneg : ∀p ∈ L, 0 ≤ p               -- separate for convenience
  normalized : L.sum = 1             -- sums to 1

def LSimplex.singleton : LSimplex [1] := 
  ⟨fun p a => by simp_all only [List.mem_cons, List.not_mem_nil, or_false, zero_le_one], 
    List.sum_singleton⟩


variable {L : List ℚ}  {c : ℚ}

theorem lsimplex_nonempty (h : LSimplex L) : L ≠ [] := 
        fun a => by have := h.normalized; simp_all 
        
abbrev LSimplex.npt : LSimplex L → L ≠ [] := lsimplex_nonempty

/-- all probability in the head -/
def LSimplex.degenerate (h : LSimplex L) : Bool := 
                           L.head (lsimplex_nonempty h) = 1

theorem lsimplex_mem_prob (h1 : LSimplex L) : ∀ p ∈ L, Prob p := 
  fun p a => ⟨ h1.nneg p a, 
               h1.normalized ▸ List.single_le_sum h1.nneg p a⟩
  
theorem lsimplex_degenerate_head_lt (S : LSimplex L) (nond : ¬S.degenerate) : L.head S.npt < 1 :=
          by have prob := lsimplex_mem_prob S (L.head S.npt) (List.head_mem (LSimplex.npt S))
             simp [LSimplex.degenerate] at nond              
             simp [Prob] at prob             
             exact lt_of_le_of_ne prob.2 nond

theorem list_scale_sum : (L.scale c).sum = c * L.sum := 
  by induction L
     · simp [List.scale]
     · simp_all [List.scale]
       ring

theorem list_scale_length : (L.scale c).length = L.length := by simp [List.scale]

theorem list_scale_nneg_of_nneg (h : ∀l ∈ L, 0 ≤ l) (h1 : 0 ≤ c) : (∀l ∈ L.scale c, 0 ≤ l) := 
  by induction L 
     · simp [List.scale]
     · simp_all [List.scale]
       exact Left.mul_nonneg h.1 h1
  
theorem list_append_nneg_of_nneg (h : ∀l ∈ L, 0 ≤ l) (h1 : 0 ≤ p) : (∀l ∈ p::L, 0 ≤ l) := 
  by aesop

/-- Adds a new probability to a list and renormalizes the rest --/
def List.spread (L : List ℚ) (p : ℚ) : List ℚ := p :: (L.scale (1-p)) 
    
theorem list_spread_sum : (L.spread p).sum = L.sum * (1-p) + p := 
  by induction L
     · simp [List.spread, List.scale]
     · simp [List.spread, list_scale_sum]
       ring

theorem list_spread_ge0 (h1 : ∀l ∈ L, 0 ≤ l)  (h2 : Prob p) :  ∀ l ∈ (L.spread p), 0 ≤ l := 
    by simp [List.spread]
       constructor
       · exact h2.1
       · intro l a
         exact list_scale_nneg_of_nneg (L := L) (c := (1-p)) 
                                       h1 (prob_of_complement h2).1 l a

theorem LSimplex.spread (S : LSimplex L) (p : ℚ) (prob : Prob p) : LSimplex (L.spread p) :=
  {nneg := list_spread_ge0 S.nneg prob,
   normalized := by simp [list_spread_sum, S.normalized]}

/-- Removes head and rescales -/
def List.unspread : List ℚ → List ℚ
    | nil => nil
    | head :: tail => tail.scale (1-head)⁻¹
    
theorem list_unspread_length : L.unspread.length = L.tail.length := 
  by cases L; simp [List.unspread]; simp[List.unspread, List.scale]
    
theorem list_unspread_sum (npt: L ≠ []) (h : L.head npt < 1) : 
        (L.unspread).sum = (L.tail).sum / (1 - L.head npt)  := 
        by cases L; contradiction; simp_all [List.unspread, list_scale_sum]; ring

theorem list_unspread_ge0 (h1 : ∀l ∈ L, Prob l) : ∀l ∈ (L.unspread), 0 ≤ l := 
    by simp [List.unspread]
       cases L with
       | nil => simp_all only [List.not_mem_nil, IsEmpty.forall_iff, implies_true]
       | cons head tail => 
           simp_all [prob_complement_inv_nneg]
           have hh : 0 ≤ (1-head)⁻¹ := prob_complement_inv_nneg h1.1
           exact list_scale_nneg_of_nneg (L:=tail) (c:=(1-head)⁻¹) (fun l a ↦ (h1.2 l a).1) hh 
         
variable {L : List ℚ}

lemma false_of_p_comp1_zero_p_less_one (h1 : 1 - p = 0) (h2 : p < 1) : False := by linarith

theorem list_spread_of_unspread 
        (npt : L ≠ [])  (le1 : L.head npt < 1) : L = (L.unspread).spread (L.head npt) := 
   by induction L with 
      | nil => have := npt rfl; contradiction
      | cons head tail => 
             let h : (1-head) ≠ 0 := fun a => false_of_p_comp1_zero_p_less_one a le1
             simp_all [List.spread, List.unspread, List.scale]
  
theorem lsimplex_tail_sum (S : LSimplex L) : L.tail.sum = (1 - L.head S.npt) := 
  by cases L; have := S.npt; contradiction; have := S.normalized; simp at this ⊢; linarith

theorem LSimplex.unspread (S : LSimplex L) (h : ¬ S.degenerate) : LSimplex (L.unspread) :=
  {nneg := list_unspread_ge0 (lsimplex_mem_prob S),
   normalized := 
     by have npt := S.npt
        have hh := lsimplex_degenerate_head_lt S h
        have hh1 := lsimplex_tail_sum S 
        have hh2 : (1 - L.head npt) ≠ 0 := by linarith
        rw[list_unspread_sum S.npt hh]
        exact (div_eq_one_iff_eq hh2).mpr hh1}

end LSimplex

section FinDist

/-- Finite probability distribution on a list (non-duplicates) -/
structure Findist (Ω : List τ) : Type where
  pr : List ℚ                      -- probability measure 
  simplex : LSimplex pr         -- proof of a measure
  unique : List.Nodup Ω            -- Ω are unique
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
     lmatch := by simp [pr', List.spread, list_scale_length, F.lmatch]}

/-- remove the head if possible -/
def Findist.unspread (h : ¬ F.simplex.degenerate): Findist (Ω.tail) :=
    let pr' := F.pr.unspread 
    let hl : pr'.length = F.pr.length - 1 := 
        by rw [list_unspread_length (L:=F.pr)]; exact List.length_tail F.pr
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

end FinDist

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
  
def Finprob.unspread (notd : ¬P.prob.simplex.degenerate) : Finprob τ := 
  { Ω := P.Ω.tail, prob := P.prob.unspread notd}
    
-- Define an induction principle for probability spaces
-- similar to the induction on lists, but also must argue about probability distributions

/-- all probability in the head -/
def Finprob.degenerate (F : Finprob τ) : Bool := F.prob.simplex.degenerate

/-- induction principle for finite probabilities -/
def Finprob.elim.{u} {motive : Finprob τ → Sort u} 
        (degenerate :  (fp : Finprob τ) → (d : fp.degenerate) → motive fp)
        (composite : (tail : Finprob τ) → (ω : τ) → (notin : ω ∉ tail.Ω) → 
                (p : ℚ) → (prob : Prob p) → motive tail → motive (tail.spread p prob ω notin)) 
        (F : Finprob τ) : motive F := 
    if b1 : F.prob.pr = [] then
      by have := lsimplex_nonempty F.prob.simplex; simp_all
    else
      if b2 : F.degenerate then
        degenerate F b2
      else
        let tail := F.unspread b2
        let ih : motive tail := Finprob.elim degenerate composite tail 
        let ω := F.Ω.head
        let p := F.prob.pr.head
        --composite tail 
        sorry
    
end Finprob

section Finrv

/-- Random variable defined on a finite probability space -/
structure Finrv (P : Finprob τ) (ρ : Type) : Type  where
  val : τ → ρ   -- actual value of the random variable

end Finrv
