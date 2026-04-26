module 
public import Mathlib.Data.Set.Defs
public import MyCGTProject.Player
public import Mathlib.Data.QPF.Univariate.Basic

import Mathlib.Data.Fintype.Defs
import Mathlib.Logic.Small.Set
import Mathlib.Data.Set.Image
import Mathlib.Data.Set.Basic
import MyCGTProject.SmallNonempty
import Mathlib.Data.Finset.Basic
import Init.Data.Bool
import Mathlib.Order.GameAdd

set_option linter.style.lambdaSyntax false
set_option linter.style.longLine false
set_option linter.unnecessarySeqFocus false

public section
-- Dicot Functor
/-- We no longer need this definition, as SCFunctor was re-defined to subsume this. However, it is nice. DicotFunctor describes the shape of composite games: games with no empty left/right sets of options. -/
private def DicotFunctor (α : Type (u + 1)) : Type (u+1):= 
{s : (Player→ Set α) | ∀ p, (Small.{u} (s p) ∧ (s p).Nonempty)}

private def DicotFunctor.map : {α : Type (u + 1)} → {β : Type (u+1)} → 
(α → β) → DicotFunctor α → DicotFunctor β := 
fun {α} {β} f s => ⟨(f '' s.1 ·), fun p =>  And.intro 
(have h1:=(s.property p).left; by infer_instance) 
(have h2 := (s.property p).right;  @Set.Nonempty.image α β (f) (s.1 p) h2 )⟩ 

private instance : Functor DicotFunctor where
map:= DicotFunctor.map


/-- Given ( A : Type), the functor "SCFunctor A" describes the shape of set coloring games. a set coloring game is either atomic (meaning a single element of a poset) or composite (a pair of non-empty sets of set coloring games). -/
@[expose]
def SCFunctor (A : Type) (α : Type (u + 1)) : Type ((u + 1)) :=
 A ⊕ {s : (Player→ Set α) | ∀ p, (Small.{u} (s p) ∧ (s p).Nonempty)}


/-- Given (A : Type), "SCFunctor A" affects morphisms as follows: it does not change the elements of A, and it changes α to β componentwise. -/
def SCFunctor.map : (A : Type) → {α : Type (u + 1)} → {β : Type (u+1)} → 
(α → β) → SCFunctor A α → SCFunctor A β := λ A {α} {β} f s => (@Sum.map.{0,0,(u + 1),(u + 1)} A A ({s : (Player→ Set α) | ∀ p, (Small.{u} (s p) ∧ (s p).Nonempty)}) ({s : (Player→ Set β) | ∀ p, (Small.{u} (s p) ∧ (s p).Nonempty)}) 
--
(@id A) (fun s => ⟨(f '' s.1 ·), fun p =>  And.intro 
(have h1:=(s.property p).left; by infer_instance) 
(have h2 := (s.property p).right;  @Set.Nonempty.image α β (f) (s.1 p) h2 )⟩)) s


instance Funct_SCFunctor : Functor (SCFunctor A) where 
map f := SCFunctor.map A f

/-- f<$> s is a notation that lean prefers, so we use this to differentiate. -/
theorem map_def {A α β} (f : α → β) (s : SCFunctor A α) :
    f <$> s = SCFunctor.map A f s := rfl 



theorem property_subsumption {A : Type} {α : Type (u + 1)} {q : α → Prop}
(st : Player → Set (Subtype q))
(hst : st ∈ {s: Player → Set (Subtype q)|∀ p, (Small.{u} (s p) ∧ (s p).Nonempty)})
(h : (λ p => Set.image Subtype.val (st p)) ∈ {s: Player→Set α| ∀ p, (Small.{u} (s p) ∧ (s p).Nonempty)}) : 
SCFunctor.map.{u} A Subtype.val (Sum.inr (⟨st,hst⟩))  = Sum.inr (⟨(λ p => Set.image Subtype.val (st p)),h⟩)
:= by congr;


-----------------------------------------------------------------------

@[expose]
def SCFunctor.P (A : Type) : PFunctor.{u + 1, u + 1} where
  A := A ⊕ (Σ (S : Player → Type u), S .left × S .right)
  B := fun
    | .inr ⟨S, _⟩ => ULift.{u + 1} (S .left ⊕ S .right)
    | .inl _ => ULift.{u + 1} Empty

def SCFunctor.absF {A : Type} {α : Type (u + 1)} :
    (SCFunctor.P.{u} A).Obj α → SCFunctor.{u} A α := fun ⟨a, f⟩ =>
  match a with
  | .inr ⟨S, sL, sR⟩ =>
    Sum.inr ⟨fun p => 
      match p with
      | .left => Set.range (f∘ULift.up∘Sum.inl)
      | .right => Set.range (f∘ULift.up∘Sum.inr),
      fun p => by
        constructor
        · match p with
        | .left => infer_instance | .right => infer_instance
        · match p with
        | .left => exact ⟨_, ⟨sL, rfl⟩⟩ | .right => exact ⟨_, ⟨sR, rfl⟩⟩
    ⟩
  | .inl a => Sum.inl a

-- def SCFunctor.qpfAbs {A : Type} {α : Type (u + 1)} :
--     (SCFunctor.P.{u} A).Obj α → SCFunctor.{u} A α :=
--   fun ⟨shape, f⟩ => match shape with
--     | Sum.inl ⟨S, hne⟩ => Sum.inl ⟨fun p => Set.range (fun s : S p => f ⟨p, s⟩),
--         fun p => ⟨@small_range.{u} (S p) α (fun s => f ⟨p, s⟩) inferInstance,
--                   ⟨f ⟨p, (hne p).some⟩, Set.mem_range_self _⟩⟩⟩
--     | Sum.inr a => Sum.inr a

noncomputable def SCFunctor.reprF {A : Type} {α : Type (u + 1)} :
    SCFunctor A α → (SCFunctor.P A).Obj α := fun
  | .inl a => ⟨.inl a, fun e => (e.down).elim⟩
  | .inr ⟨s, hs⟩ =>
    have : Small.{u} ↥(s .left) := (hs .left).1
    have : Small.{u} ↥(s .right) := (hs .right).1
    have hNL := (hs .left).2
    have hNR := (hs .right).2
    let eL := equivShrink.{u} (s .left) 
    let eR := equivShrink.{u} (s .right)
    ⟨.inr ⟨fun p => match p with
      | .left => Shrink.{u} (s .left) | .right => Shrink.{u} (s .right),
      eL ⟨hNL.some, hNL.some_mem⟩, eR ⟨hNR.some, hNR.some_mem⟩⟩,
    fun ⟨lr⟩ => match lr with
      | .inl l => (eL.symm l).val | .inr r => (eR.symm r).val
    ⟩

theorem SCFunctor.abs_repr_eq {A : Type} {α : Type (u + 1)}
    (x : SCFunctor.{u} A α) :
    SCFunctor.absF (SCFunctor.reprF x) = x := by
  cases x <;> simp only [absF, reprF]; 
  apply congr_arg Sum.inr ( Subtype.ext _ );
  ext p x; cases p <;> simp only [ Set.mem_range ] ;
  · constructor;
    · aesop;
    · exact fun hx => ⟨ _, Subtype.ext_iff.mp ( Equiv.apply_symm_apply _ ⟨ x, hx ⟩ ) ⟩;
  · constructor;
    · aesop;
    · exact fun hx => ⟨ _, Subtype.ext_iff.mp ( Equiv.apply_symm_apply _ ⟨ x, hx ⟩ ) ⟩

theorem SCFunctor.abs_map_eq {A : Type} [Small.{u + 1} A] {α β : Type (u + 1)}
    (f : α → β) (p : (SCFunctor.P.{u} A).Obj α) :
    SCFunctor.absF ((SCFunctor.P.{u} A).map f p) =
    @Functor.map _ (Funct_SCFunctor ) _ _ f (SCFunctor.absF p) := by
  rcases p with ⟨ a, f ⟩;
  unfold absF;
  rcases a with ( a | ⟨ S, sL, sR ⟩ );
  · rfl
  · simp only [ PFunctor.map ];
    congr;
    ext p; cases p <;> simp [ Set.range ] ;


noncomputable instance QPF_SCFunctor (A : Type) :
    QPF (SCFunctor A) where
  toFunctor := Funct_SCFunctor 
  P := SCFunctor.P A
  abs := SCFunctor.absF
  repr := SCFunctor.reprF
  abs_repr := SCFunctor.abs_repr_eq
  abs_map := SCFunctor.abs_map_eq
