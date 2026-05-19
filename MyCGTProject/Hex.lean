-- This is code that describes a lot of the operations on games of Hex.
import Mathlib.Logic.Small.Set
import Mathlib.Data.Set.Image
import Mathlib.Data.Set.Basic
import MyCGTProject.Primordial
import MyCGTProject.Basic
import Mathlib.Order.GameAdd
set_option linter.style.lambdaSyntax false
set_option linter.style.longLine false
set_option linter.unnecessarySeqFocus false
--set_option trace.Meta.synthInstance true

universe u

open Primordial

def pGoal (p : Player) : Bool := 
match p with
| left => ⊤
|right => ⊥

lemma pGoal_neg (p : Player) : pGoal (p) ≠ pGoal (-p) := by
  cases p
  case' left => rw [Player.neg_left]
  case' right =>  rw [Player.neg_right] ; symm
  
  all_goals
    repeat rw [pGoal]
    trivial


mutual
/-- First player winning strategy in x for player p. -/
def FPS (x : Primordial Bool) (p : Player) : Prop := (∃ h : IsAtom x, Sum.getLeft (moves_or x) h = pGoal p) ∨ (∃ y, ∃ _: y∈ moves x p, SPS y p) 
termination_by x
decreasing_by Primordial_wf

/-- Second player winning strategy in x for player p. -/
def SPS (x : Primordial Bool) (p:Player) : Prop := 
  (∀ h:IsAtom x, Sum.getLeft (moves_or x) h = pGoal p)∧ (∀ y, y∈ moves x (-p) → FPS y p)
termination_by x
decreasing_by Primordial_wf

end

abbrev oc (x : Primordial Bool) : Prop × Prop := (FPS x left, SPS x left)

abbrev eval {A B : Type} {p : (A → B) → Prop} (xf : A × {f:A → B| p f}) : B := xf.2.1 xf.1 


--contextual order on games
def contxRel {A : Type} [Preorder A] (g h : Primordial.{u} A) : Prop := ∀ x : Primordial.{u} ({f : A → Bool | Monotone f}), oc (MAP eval (g + x)) ≤ oc (MAP eval (h + x))


-- at some point I want to create the notation `≤ᶜ` for contextual relation, but this is a projcect for later.
instance contx.LE {A : Type} [Preorder A] : LE (Primordial.{u} A) where
le := contxRel

-- lemma contx.format {A : Type} [Preorder A] {x y : Primordial A} : x ≤ y ↔ contxRel x y := by rfl

instance {A : Type} [Preorder A] : Preorder (Primordial A) where
  le_refl _:= by
          intro _
          rfl
  le_trans _ _ _ h1 h2 x := by
           specialize h1 x  
           specialize h2 x
           -- this le_trans applies to the relation on Prop×Prop.
           apply le_trans h1 h2

example {A : Type} [Preorder A] {x : Primordial A} : x ≤ x := by rfl


/-- fundamental theorem: If Left has a first player winning strategy 
then right cannot have a seccond player winning stategy. -/
theorem fundCGT (x : Primordial Bool) : ∀ p, FPS x p ↔ ¬ (SPS x (-p)):= by 
  intro p
  rw [FPS,SPS]
  rw [not_and_or]
  conv =>
      right
      repeat rw [not_forall]
  constructor
  · intro h'
    cases h'
    case inl h' =>
      left
      obtain ⟨ha,a⟩ := h'
      use ha
      rw [a]
      apply pGoal_neg
    case inr h' =>
      right  
      obtain ⟨a,⟨ham,has⟩⟩ := h'
      use a
      rw [neg_neg, Classical.not_imp]
      apply not_not.mpr at has
      rw [← neg_neg p] at has
      rw [← fundCGT] at has
      exact ⟨ham,has⟩
  · intro h'
    cases h'
    case inl h' =>
      left 
      obtain ⟨ha,a⟩:= h'
      use ha
      by_contra 
      cases hx :(moves_or x).getLeft ha
      all_goals
          rw [hx] at this a
          simp_all only [Bool.false_eq, Bool.not_eq_false, Sum.getLeft_eq_iff]
          have this' : pGoal p = pGoal (-p) := by aesop
          have := pGoal_neg p
          contradiction
    case inr h' =>      
      right  
      obtain ⟨a,ham⟩ := h'
      use a
      rw [neg_neg, Classical.not_imp] at ham
      obtain ⟨ham1,ham2⟩ := ham
      use ham1
      rw [fundCGT] at ham2
      rw [neg_neg p,not_not] at ham2
      exact ham2
termination_by x
decreasing_by Primordial_wf

theorem fundCGTv2 (x : Primordial Bool) : ∀ p, SPS x p ↔ ¬ (FPS x (-p)):= by 
  intro p
  have :=(fundCGT x (-p)).symm
  rw [neg_neg] at this
  rw [← not_iff] at this
  rw [Classical.not_iff] at this
  exact iff_not_comm.mp (id (Iff.symm this))
