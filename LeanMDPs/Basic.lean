import Mathlib.Data.Nat.Defs


/--
inductive Hist (α σ : Type) : Type where
  | init (s : σ) : Hist α σ
  | app (head : Hist α σ) (a : α) (s : σ) : Hist α σ
-/

structure Hist (α σ : Type) : Type where
  mk ::
  init : σ
  tail : List (α × σ)

def Hist.length {α σ : Type} (h : Hist α σ) : ℕ := List.length h.tail




#check Set

#check Decidable False

inductive Hprefix {α σ : Type} (p h: Hist α σ) 

/--
verifies that 
-/
---def History.prefix {α σ : Type} (pre : Hist α σ) : Hist α σ → Prop :=
    


example : True := True.intro

variable (a b : Prop) 

example (h: a ∧ b) : a := h.left
example (h: a ∧ b) : b := h.right

variable (cons prop : Prop)

example (h1 : cons → prop) : ¬ (prop → cons) := sorry
        

