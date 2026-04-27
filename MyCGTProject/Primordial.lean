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


/-- Given ( A : Type), the functor "Primordial A" maps  α :Type u to the direct sum of A and pairs of Set (α). This is close to the shape of set coloring games (in set coloring games we require option sets to be non-empty as well. -/
@[expose]
def Primordial (A : Type) (α : Type (u + 1)) : Type ((u + 1)) :=
 A ⊕ {s : (Player→ Set α) | ∀ p, Small.{u} (s p)}


/-- Given (A : Type), "SCFunctor A" affects morphisms as follows: it does not change the elements of A, and it changes α to β componentwise. -/
def Primordial.map : (A : Type) → {α : Type (u + 1)} → {β : Type (u+1)} → 
(α → β) → Primordial A α → Primordial A β := λ A {α} {β} f s => (@Sum.map.{0,0,(u + 1),(u + 1)} A A ({s : (Player→ Set α) | ∀ p, Small.{u} (s p)}) ({s : (Player→ Set β) | ∀ p, Small.{u} (s p) }) 
--
(@id A) (fun s => ⟨(f '' s.1 ·), fun p => (have h1:= (s.property p); by infer_instance)⟩)) s


instance Funct_Primordial : Functor (Primordial A) where 
map f := Primordial.map A f

/-- f<$> s is a notation that lean prefers, so we use this to differentiate. -/
theorem map_def {A α β} (f : α → β) (s : Primordial A α) :
    f <$> s = Primordial.map A f s := rfl 


-----------------------------------------------------------------------

@[expose]
def Primordial.P (A : Type) : PFunctor.{u + 1, u + 1} where
  A := A ⊕ ( Player → Type u)
  B := fun
    | .inr S => ULift.{u + 1} (S .left ⊕ S .right)
    | .inl _ => ULift.{u + 1} Empty

def Primordial.absF {A : Type} {α : Type (u + 1)} :
    (Primordial.P.{u} A).Obj α → Primordial.{u} A α := fun ⟨a, f⟩ =>
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

noncomputable def Primordial.reprF {A : Type} {α : Type (u + 1)} :
    Primordial A α → (Primordial.P A).Obj α := fun
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

theorem Primordial.abs_repr_eq {A : Type} {α : Type (u + 1)}
    (x : Primordial.{u} A α) :
    Primordial.absF (Primordial.reprF x) = x := by
  cases x <;> simp only [absF, reprF]; 
  apply congr_arg Sum.inr ( Subtype.ext _ );
  ext p x; cases p <;> simp only [ Set.mem_range ] ;
  · constructor;
    · aesop;
    · exact fun hx => ⟨ _, Subtype.ext_iff.mp ( Equiv.apply_symm_apply _ ⟨ x, hx ⟩ ) ⟩;
  · constructor;
    · aesop;
    · exact fun hx => ⟨ _, Subtype.ext_iff.mp ( Equiv.apply_symm_apply _ ⟨ x, hx ⟩ ) ⟩

theorem Primordial.abs_map_eq {A : Type} [Small.{u + 1} A] {α β : Type (u + 1)}
    (f : α → β) (p : (Primordial.P.{u} A).Obj α) :
    Primordial.absF ((Primordial.P.{u} A).map f p) =
    @Functor.map _ (Funct_Primordial ) _ _ f (Primordial.absF p) := by
  rcases p with ⟨ a, f ⟩;
  unfold absF;
  rcases a with ( a | S );
  · rfl
  · simp only [ PFunctor.map ];
    congr;
    ext p; cases p <;> simp [ Set.range ] ;


noncomputable instance QPF_Primordial (A : Type) :
    QPF (Primordial A) where
  toFunctor := Funct_Primordial 
  P := Primordial.P A
  abs := Primordial.absF
  repr := Primordial.reprF
  abs_repr := Primordial.abs_repr_eq
  abs_map := Primordial.abs_map_eq

