import Mathlib.Data.Fintype.Defs
import Mathlib.Logic.Small.Set
import Mathlib.Data.TypeVec
import Mathlib.Control.Functor.Multivariate
import Mathlib.Data.QPF.Univariate.Basic
import Mathlib.Data.Set.Image
import Mathlib.Data.Set.Basic
import MyCGTProject.Player
import Mathlib.Data.Finset.Basic

set_option linter.style.lambdaSyntax false
set_option linter.style.longLine false
set_option linter.unnecessarySeqFocus false
--set_option trace.Meta.synthInstance true

universe u v


inductive listGame (α : Type u) where
| atom : α → listGame α 
| game : (List (listGame α)) → (List (listGame α))→ listGame α

-- inductive Player where
-- | left: Player
-- | right: Player

-- The following definition does not work, as it is non-positive (and lean tells us this). 
-- inductive badSetGame (α : Type u) where
-- | atom : α → badSetGame α 
-- | game : (Set (badSetGame α)) → (Set (badSetGame α))→ badSetGame α



-- now defining the QPF!!!


-- Dicot Functor
def DicotFunctor (α : Type (u + 1)) : Type (u+1):= 
{s : (Player→ Set α) | ∀ p, (Small.{u} (s p) ∧ (s p).Nonempty)}

def DicotFunctor.map : {α : Type (u + 1)} → {β : Type (u+1)} → 
(α → β) → DicotFunctor α → DicotFunctor β := 
fun {α} {β} f s => ⟨(f '' s.1 ·), fun p =>  And.intro 
(have h1:=(s.property p).left; by infer_instance) 
(have h2 := (s.property p).right;  @Set.Nonempty.image α β (f) (s.1 p) h2 )⟩ 

instance : Functor DicotFunctor where
map:= DicotFunctor.map

def SCFunctor (A : Type) (α : Type (u + 1)) : Type ((u + 1)) :=
 A ⊕ (DicotFunctor α)

instance Funct_SCFunctor : Functor (SCFunctor A) where 
map f := Sum.map (@id A) (DicotFunctor.map f)  

theorem map_def {A α β} (f : α → β) (s : SCFunctor A α) :
    f <$> s = Sum.map (@id A) (DicotFunctor.map f) s:=
  rfl


-----------------------------------------------------------------------


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


def Hex (A : Type) : Type (u + 1) := @QPF.Fix (SCFunctor A) (QPF_SCFunctor A)

noncomputable def moves_or {A : Type} : Hex A → A ⊕ {s : (Player→ Set (Hex A)) // ∀ p, (Small.{u} (s p) ∧ (s p).Nonempty)} :=
  fun x =>@QPF.Fix.dest (SCFunctor A) (QPF_SCFunctor A) x

noncomputable def AtomSC (A : Type) := {x: Hex A | Sum.isLeft (moves_or x)}
noncomputable def CompSC (A : Type) := {x : Hex A | Sum.isRight (moves_or x)}
    
noncomputable def mk_atom {A : Type} : A → AtomSC A := fun a => 
@Subtype.mk (Hex A) (λ g => Sum.isLeft (moves_or g))
(@QPF.Fix.mk (SCFunctor A) (QPF_SCFunctor A) (@Sum.inl A {st : Player → Set (Hex A) // ∀ p, Small (st p) ∧ (st p).Nonempty} a))
 (by congr)

noncomputable def mk_comp {A : Type} (s : {st : Player → Set (Hex A) // ∀ p, Small (st p) ∧ (st p).Nonempty}) : CompSC A :=
  @Subtype.mk (Hex A) (λ g => Sum.isRight (moves_or g))
    (@QPF.Fix.mk (SCFunctor A) (QPF_SCFunctor A) (@Sum.inr A {st : Player → Set (Hex A) // ∀ p, Small (st p) ∧ (st p).Nonempty} s))
    (by congr)
theorem mk_moves_or_id {A : Type} (x : Hex A) : QPF.Fix.mk (moves_or x) = x:= by 
  dsimp [moves_or]
  rw [QPF.Fix.mk_dest]


theorem mk_atom_moves_or_id {A : Type} (x : AtomSC A) : mk_atom (Sum.getLeft (moves_or x.1) x.2) = x := by 
  unfold mk_atom
  congr
  rw [Sum.inl_getLeft, mk_moves_or_id]

theorem mk_comp_moves_or_id {A : Type} (x : CompSC A) : mk_comp (Sum.getRight (moves_or x.1) x.2) = x := by 
  unfold mk_comp
  congr
  rw [Sum.inr_getRight, mk_moves_or_id]


theorem moves_or_mk_comp_id {A : Type} (st : Player → Set (Hex A)) (h : ∀ p, Small (st p) ∧ (st p).Nonempty) : moves_or (mk_comp ⟨st, h⟩) = Sum.inr ⟨st, h⟩ := by 
  dsimp [moves_or,mk_comp]
  rw [QPF.Fix.dest_mk] 


theorem moves_or_mk_atom_id {A : Type} (x : A) : moves_or (mk_atom x) = Sum.inl x
:= by 
  dsimp [moves_or,mk_atom]
  rw [QPF.Fix.dest_mk] 

-- Special Games
noncomputable def is_atomic {A : Type} : (Hex A) → Bool := λ g => Sum.isLeft (moves_or g)
noncomputable def is_composite {A : Type} : ( Hex A) → Bool := λ g => Sum.isRight (moves_or g)



namespace Hex
export Player (left right)
noncomputable section

-----------------------------------------------------------------------------------

/-! ### OfSetsSC -/


/--
definition  of the `ofSetsSC` operation.
Used to implement the `!{st}` and `!{s | t}` syntax.
Here we construct a combinatorial Set Coloring game from its left and right sets. -/
def ofSetsSC {A : Type} (st : Player → Set (Hex A)) [Small.{u} (st left)] [Nonempty (st left)] [Small.{u} (st right)] [Nonempty (st right)] : CompSC A := 
    @Subtype.mk (Hex A) (λ x => Sum.isRight (moves_or x)) (@mk_comp A ⟨st , 
      λ p => match p with
        |left => ⟨by assumption,(have h := Iff.mp (Set.nonempty_coe_sort); by apply h; assumption)⟩
        |right => ⟨by assumption,(have h := Iff.mp (Set.nonempty_coe_sort); by apply h; assumption)⟩⟩)
    (by congr)
    

@[inherit_doc Hex.ofSetsSC]
macro "!{" st:term:max "}"  : term => `(Hex.ofSetsSC $st)

@[inherit_doc Hex.ofSetsSC]
macro "!{" s:term " | " t:term "}" : term => `(!{(Player.cases $s $t)})


recommended_spelling "ofSetsSC" for "!{st}" in [Hex.ofSetsSC, «term!{_}»]
recommended_spelling "ofSetsSC" for "!{s | t}" in [Hex.ofSetsSC, «term!{_|_}»]

open Lean PrettyPrinter Delaborator SubExpr in
/-- Delaborates `ofSetsSC (Player.cases s t)` to `!{s | t}` and `ofSetsSC st` to `!{st}`. -/
@[app_delab Hex.ofSetsSC]
meta def delabOfSetsSC : Delab := do
  let e ← getExpr
  guard <| e.isAppOfArity' ``Hex.ofSetsSC 7
  withNaryArg 3 do
    let e ← getExpr
    if e.isAppOfArity' ``Player.cases 3 then
      let s ← withNaryArg 1 delab
      let t ← withNaryArg 2 delab
      `(!{$s | $t})
    else
      let st ← delab
      `(!{$st})
 
theorem ofSetsSC_eq_ofSetsSC_cases {A : Type} (st : Player → Set (Hex.{u} A)) [Small.{u} (st left)] [Nonempty (st left)] [Small.{u} (st right)] [Nonempty (st right)] :
    !{st} = !{(st left) | (st right)} := by
    congr; ext1 p; cases p <;> rfl


/-- The set of moves of a composite game. -/
def moves {A : Type} (x : CompSC A) (p : Player) : Set (Hex A) :=  
  (@Sum.getRight A {st : Player → Set (Hex A) // ∀ p, Small (st p) ∧ (st p).Nonempty} (moves_or x.1) x.2).1 p

/-- The set of left moves of a composite game. -/
notation x:max "ᴸ" => moves x left 

/-- The set of right moves of a composite game. -/
notation x:max "ᴿ" => moves x right 

instance {A : Type} (p : Player) (x : CompSC.{u} A) : Small.{u} (moves x p) := 
  let g:= Sum.getRight (moves_or x.1) x.2; 
  have he : g.1 p = moves x p := by rfl;
  let hg := And.left (g.2 p);
  by 
  rw [he] at hg 
  exact hg;

instance {A : Type} (p : Player) (x : CompSC.{u} A) : Nonempty (moves x p) := 
  let g:= Sum.getRight (moves_or x.1) x.2; 
  have he : g.1 p = moves x p := by rfl;
  let hg := And.right (g.2 p);
  have h := Iff.mpr (Set.nonempty_coe_sort);
  by 
  rw [he] at hg 
  apply h at hg
  exact hg;



@[simp]
theorem moves_ofSets {A : Type} (st : Player → Set (Hex A)) (p : Player) [Small.{u} (st left)] [Nonempty (st left)] [Small.{u} (st right)] [Nonempty (st right)] :
   moves !{st} p = st p := by 
  dsimp [ofSetsSC, moves]  
  simp [moves_or_mk_comp_id]


@[simp]
theorem ofSets_moves {A : Type} (x : CompSC A) : !{(moves x)}  = x := by
  dsimp [ ofSetsSC]
  unfold moves
  rw [Subtype.eta] 
  rw [mk_comp_moves_or_id]

theorem leftMoves_ofSets (s t : Set (Hex A)) [Small.{u} s] [Nonempty s] [Small.{u} t] [Nonempty t] : !{s|t}ᴸ = s :=  
moves_ofSets ..

theorem rightMoves_ofSets (s t : Set (Hex A)) [Small.{u} s] [Nonempty s] [Small.{u} t] [Nonempty t] : !{s|t}ᴿ = t :=  
moves_ofSets ..

@[simp]
theorem ofSets_leftMoves_rightMoves (x : CompSC A) : !{xᴸ | xᴿ} = x :=  by 
  convert (ofSets_moves x) with p
  funext p
  cases p <;> dsimp [Player.cases]

@[ext]
theorem ext {A : Type} {x y : CompSC A} (h : ∀ p, moves x p = moves y p) : x = y :=  by 
    rw [← ofSets_moves x , ← ofSets_moves y ]
    simp_rw [funext h] 
    
       
@[simp]
theorem ofSets_inj' {A : Type} {st₁ st₂ : Player → Set (Hex A)}
    [Small (st₁ left)] [Small (st₁ right)] [Small (st₂ left)] [Small (st₂ right)] [Nonempty (st₁ left)] [Nonempty (st₁ right)] [Nonempty (st₂ left)] [Nonempty (st₂ right)] :
    !{st₁} =!{st₂}↔ st₁ = st₂ := by
    simp_rw [Hex.ext_iff, moves_ofSets, funext_iff]

theorem ofSets_inj {A : Type} {s₁ s₂ t₁ t₂ : Set (Hex A)} [Small s₁] [Small s₂] [Small t₁] [Small t₂] [Nonempty s₁] [Nonempty s₂] [Nonempty t₁] [Nonempty t₂] :
    !{s₁ | t₁} = !{s₂ | t₂} ↔ s₁ = s₂ ∧ t₁ = t₂ := by
  simp



/-- option x y : x is in the left or right set of the (composite) game y. -/
def option {A : Type} : (Hex A) → (CompSC A) → Prop := fun x y => x ∈ ⋃ p, (moves y) p

/-- A proper subposition of a (composite) game y is any game reachable by a nonempty sequence of left and right moves. -/
inductive Subposition {A : Type} : (Hex A) → (CompSC A) -> Prop where
| single {a:Hex A} {b:CompSC A} : option a b → Subposition a b
| tail {a:Hex A} {b c : CompSC A}: Subposition a b → option (b.val) c → Subposition a c

@[aesop unsafe apply 50%]
theorem Subposition.of_mem_moves {A : Type} {p} {x : Hex A} {y : CompSC A} (h : x ∈ moves y p) : Subposition x y :=
  Subposition.single (Set.mem_iUnion_of_mem p h)

/-- transitivity of Subposition relation -/
theorem Subposition.trans {A : Type} {a : Hex A} {b c : CompSC A} : Subposition a b → Subposition b.val c -> Subposition a c := by 
  intro hab hbc
  induction hbc with
  | @single c h => exact Subposition.tail hab h
  | @tail x c _ h ih => exact Subposition.tail ih h

-- unfortunately we cannot define an instance of "IsTrans" because of the subtype nature of our definition. We will be able to give an instance of IsTrans for the definition of followers.

end
end Hex

-- SCFunctor ()



-- def D := Unit
-- def z:Unit := Unit.unit





