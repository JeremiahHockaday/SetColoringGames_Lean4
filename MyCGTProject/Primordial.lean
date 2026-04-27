module 
public import Mathlib.Data.Set.Defs
public import MyCGTProject.Player
public import Mathlib.Data.QPF.Univariate.Basic

import Mathlib.Logic.Small.Set
import Mathlib.Data.Set.Image
import Mathlib.Data.Set.Basic
import MyCGTProject.SmallNonempty

set_option linter.style.lambdaSyntax false
set_option linter.style.longLine false
set_option linter.unnecessarySeqFocus false

public section


/-- Given ( A : Type), the functor "PrimordialFunctor A" maps  α :Type u to the direct sum of A and pairs of Set (α). This is close to the shape of set coloring games (in set coloring games we require option sets to be non-empty as well. -/
@[expose]
def PrimordialFunctor (A : Type) (α : Type (u + 1)) : Type ((u + 1)) :=
 A ⊕ {s : (Player→ Set α) | ∀ p, Small.{u} (s p)}


/-- Given (A : Type), "SCFunctor A" affects morphisms as follows: it does not change the elements of A, and it changes α to β componentwise. -/
def PrimordialFunctor.map : (A : Type) → {α : Type (u + 1)} → {β : Type (u+1)} → 
(α → β) → PrimordialFunctor A α → PrimordialFunctor A β := λ A {α} {β} f s => (@Sum.map.{0,0,(u + 1),(u + 1)} A A ({s : (Player→ Set α) | ∀ p, Small.{u} (s p)}) ({s : (Player→ Set β) | ∀ p, Small.{u} (s p) }) 
--
(@id A) (fun s => ⟨(f '' s.1 ·), fun p => (have h1:= (s.property p); by infer_instance)⟩)) s


instance Funct_PrimordialFunctor : Functor (PrimordialFunctor A) where 
map f := PrimordialFunctor.map A f

/-- f<$> s is a notation that lean prefers, so we use this to differentiate. -/
theorem PrimordialFunctor.map_def {A α β} (f : α → β) (s : PrimordialFunctor A α) :
    f <$> s = PrimordialFunctor.map A f s := rfl 


-----------------------------------------------------------------------

@[expose]
def PrimordialFunctor.P (A : Type) : PFunctor.{u + 1, u + 1} where
  A := A ⊕ ( Player → Type u)
  B := fun
    | .inr S => ULift.{u + 1} (S .left ⊕ S .right)
    | .inl _ => ULift.{u + 1} Empty

def PrimordialFunctor.absF {A : Type} {α : Type (u + 1)} :
    (PrimordialFunctor.P.{u} A).Obj α → PrimordialFunctor.{u} A α := fun ⟨a, f⟩ =>
  match a with
  | .inr S =>
    Sum.inr ⟨fun p => 
      match p with
      | .left => Set.range (f∘ULift.up∘Sum.inl)
      | .right => Set.range (f∘ULift.up∘Sum.inr),
      fun p => by
         match p with
        | .left => infer_instance | .right => infer_instance
    ⟩
  | .inl a => Sum.inl a

noncomputable def PrimordialFunctor.reprF {A : Type} {α : Type (u + 1)} :
    PrimordialFunctor A α → (PrimordialFunctor.P A).Obj α := fun
  | .inl a => ⟨.inl a, fun e => (e.down).elim⟩
  | .inr ⟨s, hs⟩ =>
    have : Small.{u} ↥(s .left) := (hs .left)
    have : Small.{u} ↥(s .right) := (hs .right)
    let eL := equivShrink.{u} (s .left) 
    let eR := equivShrink.{u} (s .right)
    ⟨.inr (fun p => match p with
      | .left => Shrink.{u} (s .left) | .right => Shrink.{u} (s .right)),
    fun ⟨lr⟩ => match lr with
      | .inl l =>  (eL.symm l).val | .inr r => (eR.symm r).val
    ⟩

theorem PrimordialFunctor.abs_repr_eq {A : Type} {α : Type (u + 1)}
    (x : PrimordialFunctor.{u} A α) :
    PrimordialFunctor.absF (PrimordialFunctor.reprF x) = x := by
  cases x <;> simp only [absF, reprF]; 
  apply congr_arg Sum.inr ( Subtype.ext _ );
  ext p x; cases p <;> simp only [ Set.mem_range ] ;
  · constructor;
    · aesop;
    · exact fun hx => ⟨ _, Subtype.ext_iff.mp ( Equiv.apply_symm_apply _ ⟨ x, hx ⟩ ) ⟩;
  · constructor;
    · aesop;
    · exact fun hx => ⟨ _, Subtype.ext_iff.mp ( Equiv.apply_symm_apply _ ⟨ x, hx ⟩ ) ⟩

theorem PrimordialFunctor.abs_map_eq {A : Type} [Small.{u + 1} A] {α β : Type (u + 1)}
    (f : α → β) (p : (PrimordialFunctor.P.{u} A).Obj α) :
    PrimordialFunctor.absF ((PrimordialFunctor.P.{u} A).map f p) =
    @Functor.map _ (Funct_PrimordialFunctor ) _ _ f (PrimordialFunctor.absF p) := by
  rcases p with ⟨ a, f ⟩;
  unfold absF;
  rcases a with ( a | S );
  · rfl
  · simp only [ PFunctor.map ];
    congr;
    ext p; cases p <;> simp [ Set.range ] ;


noncomputable instance QPF_PrimordialFunctor (A : Type) :
    QPF (PrimordialFunctor A) where
  toFunctor := Funct_PrimordialFunctor 
  P := PrimordialFunctor.P A
  abs := PrimordialFunctor.absF
  repr := PrimordialFunctor.reprF
  abs_repr := PrimordialFunctor.abs_repr_eq
  abs_map := PrimordialFunctor.abs_map_eq

