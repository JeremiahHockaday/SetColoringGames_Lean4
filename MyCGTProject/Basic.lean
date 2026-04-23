import Mathlib.Data.Fintype.Defs
import Mathlib.Logic.Small.Set
import Mathlib.Data.QPF.Univariate.Basic
import Mathlib.Data.Set.Image
import Mathlib.Data.Set.Basic
import MyCGTProject.Player
import MyCGTProject.Small
import Mathlib.Data.Finset.Basic


set_option linter.style.lambdaSyntax false
set_option linter.style.longLine false
set_option linter.unnecessarySeqFocus false
--set_option trace.Meta.synthInstance true

universe u


-- The following definition does not work, as it is non-positive (and lean tells us this). 
-- inductive badSetGame (α : Type u) where
-- | atom : α → badSetGame α 
-- | game : (Set (badSetGame α)) → (Set (badSetGame α))→ badSetGame α


instance small_isEmpty {α : Type (u + 1)} [IsEmpty α] : Small.{u} α := by 
  let f : α→Unit := λ _ => Unit.unit;
  infer_instance;

@[reducible]
noncomputable def Nonempty_equiv (α) {β} [inst : Nonempty α] (h : Equiv α β) : Nonempty β := 
  let x := Classical.choice (inst);
  let h' := Equiv.toFun h;
  Nonempty.intro (h' x) 
-- now defining the QPF!!!



def sub_temp_left {α : Type (u + 1)} (p : α → Prop) (X : Set (Subtype p)) : X→ Set.image Subtype.val X := λ x => ⟨x.val, by 
    let ⟨⟨a,ha⟩,hy⟩ := x;
    simp only [Set.mem_image, Subtype.exists, exists_and_right, exists_eq_right]
    constructor
    · exact hy
    · exact ha 
    ⟩

def sub_temp_right {α : Type (u + 1)} (p : α → Prop) (X : Set (Subtype p)) : Set.image Subtype.val X → X := λ x => ⟨⟨x.val, by 
    let ⟨a,⟨⟨b1,b2⟩,⟨hb1,hb2⟩⟩⟩ := x;
    simp only at hb2
    simp only [hb2] at b2
    simp only
    exact b2⟩, by
      let ⟨a,⟨⟨b1,b2⟩,⟨hb1,hb2⟩⟩⟩ := x;
      simp only at hb2
      have hn : p a := by 
        rw [hb2] at b2
        exact b2
      have hx : Subtype.mk b1 b2 = ⟨a,hn⟩:= by
        ext
        simp only
        exact hb2;
      simp [← hx, hb1]⟩

def subtype_set_im_equiv {α : Type (u + 1)} (p : α → Prop) (X : Set (Subtype p)) : Equiv X (Set.image Subtype.val X) := 
  ⟨sub_temp_left p X 
  ,
  sub_temp_right p X
  , 
  by
  intro x
  simp only [sub_temp_right,sub_temp_left]
  , 
  by
  intro x
  simp only [sub_temp_right, sub_temp_left, Subtype.coe_eta]
  ⟩

instance subtype_set_small {α : Type (u + 1)} (p : α → Prop) (X : Set (Subtype p)) [Small.{u} X] : Small.{u} (Set.image Subtype.val X):= by 
  let f := sub_temp_left p X;
  have hg : Function.Injective (sub_temp_right p X) := by
    intro b c hi
    simp only [sub_temp_right,Subtype.mk.injEq] at hi
    ext 
    rw [hi]
  exact small_of_injective (hg)

-- Dicot Functor
/-- We no longer need this definition, as SCFunctor was re-defined to subsume this. However, it is nice. DicotFunctor describes the shape of composite games: games with no empty left/right sets of options. -/
def DicotFunctor (α : Type (u + 1)) : Type (u+1):= 
{s : (Player→ Set α) | ∀ p, (Small.{u} (s p) ∧ (s p).Nonempty)}

def DicotFunctor.map : {α : Type (u + 1)} → {β : Type (u+1)} → 
(α → β) → DicotFunctor α → DicotFunctor β := 
fun {α} {β} f s => ⟨(f '' s.1 ·), fun p =>  And.intro 
(have h1:=(s.property p).left; by infer_instance) 
(have h2 := (s.property p).right;  @Set.Nonempty.image α β (f) (s.1 p) h2 )⟩ 

instance : Functor DicotFunctor where
map:= DicotFunctor.map


/-- Given ( A : Type), the functor "SCFunctor A" describes the shape of set coloring games. a set coloring game is either atomic (meaning a single element of a poset) or composite (a pair of non-empty sets of set coloring games). -/
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
noncomputable def casesSC {A : Type} {α : (Hex.{u} A) → Prop} (ha : ∀ a : AtomSC A, α a.1) (hc : ∀ g : CompSC A, α g.1) ( x : (Hex.{u} A)): α x := by
  cases h : Sum.isRight (moves_or x)
  ·have h1 : (moves_or x).isLeft := Sum.isRight_eq_false.mp h;
   exact (ha ⟨x,h1⟩)
  ·exact (hc ⟨x,h⟩)

theorem Atom_nComp_iff {A : Type} {x : Hex A} : x∈ AtomSC A ↔ x ∉CompSC A := by
  dsimp [CompSC] 
  dsimp [AtomSC]
  constructor
  · intro ha
    simp only [Bool.not_eq_true, Sum.isRight_eq_false]
    exact ha
  · intro nhc
    simp only [Bool.not_eq_true, Sum.isRight_eq_false] at nhc
    exact nhc
theorem Comp_nAtom_iff {A : Type} {x : Hex A} : x∈ CompSC A ↔ x ∉AtomSC A := by
  dsimp [CompSC]
  dsimp [AtomSC]
  constructor
  · intro nhc
    simp only [Bool.not_eq_true, Sum.isLeft_eq_false]
    exact nhc
  · intro ha
    simp only [Bool.not_eq_true, Sum.isLeft_eq_false] at ha
    exact ha


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

instance small_moves {A : Type} (p : Player) (x : CompSC.{u} A) : Small.{u} (moves x p) := 
  let g:= Sum.getRight (moves_or x.1) x.2; 
  have he : g.1 p = moves x p := by rfl;
  let hg := And.left (g.2 p);
  by 
  rw [he] at hg 
  exact hg;

instance nonempty_moves {A : Type} (p : Player) (x : CompSC.{u} A) : Nonempty (moves x p) := 
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


-- Because of the diffference between composite and atomic games, we must define subpositions very carefully.


/-- option x y : y is composite and x is in the left or right set of the game y. -/
def option {A : Type} : (Hex.{u} A) → (Hex.{u} A) → Prop := fun x y => ∃ h:y ∈ CompSC.{u} A, x ∈ ⋃ p, (moves.{u} ⟨y,h⟩) p

/-- A proper subposition of a (composite) game y is any game reachable by a nonempty sequence of left and right moves. -/
def Subposition {A : Type} : (Hex A) -> (Hex A) -> Prop := Relation.TransGen option

@[aesop unsafe apply 50%]
theorem Subposition.of_mem_moves {A : Type} {x : Hex A} {y : CompSC A} (h : x ∈ ⋃ p, (moves.{u} y) p) : Subposition x y.1 :=
  Relation.TransGen.single (by 
    unfold option
    have h':y.1∈ CompSC A := by 
      simp
    use h')

/-- transitivity of Subposition relation -/
theorem Subposition.trans {A : Type} {a b c : Hex A} : Subposition a b → Subposition b c -> Subposition a c := Relation.TransGen.trans

instance {A : Type} : IsTrans (Hex A) Subposition := inferInstanceAs (IsTrans _ (Relation.TransGen _))
  

instance comp.small_setOf_options {A : Type} : 
∀ x : (CompSC.{u} A),  Small.{u , u + 1} {y : Hex A | y ∈ ⋃ p, (moves x) p} := 
  λ x =>
  have h1 : Small.{u} (⋃ p, (moves x) p) := by infer_instance;
  let f : {y : Hex A | y ∈ ⋃ p, (moves x) p} → ⋃ p, (moves x) p := λ x => x;
  let g : ⋃ p, (moves x) p→{y : Hex A | y ∈ ⋃ p, (moves x) p} := λ x => x;
  have h3 : g∘f = id := by congr;
  have h4 : Function.LeftInverse g f := by 
    dsimp [Function.LeftInverse]
    intro x
    congr;
  small_of_injective (Function.LeftInverse.injective h4)

instance Atom_no_options {A : Type} (x : Hex.{u} A) (h : Sum.isLeft (moves_or x)) : IsEmpty {y : Hex A // y.option x}:=
have h1 := Sum.isRight_eq_false.mpr h;
    have h2 : x ∉ CompSC.{u} A  := by 
      false_or_by_contra
      have h2a : Sum.isRight (moves_or x) := by congr;
      have h2b : true = false := by 
        have h2c : x=x := rfl;
        apply @congrArg _ _ x x ( Sum.isRight∘(@moves_or A)) at h2c 
        dsimp [Function.comp] at h2c
        nth_rewrite 1 [h2a] at h2c
        rw [h1] at h2c
        exact h2c
      contradiction;
    have h3 : ∀ y : {y : Hex A | option y x}, False := by 
      intro ⟨y,a⟩
      apply Exists.nonempty at a;
      apply (@nonempty_prop (x ∈ CompSC A)).mp at a;
      contradiction;
    by exact (isEmpty_iff.mpr h3)

instance small_setOf_options {A : Type} : ∀ x : (Hex.{u} A),  Small.{u , u + 1} {y : Hex A // y.option x} := λ x => by 
  dsimp [option]
  cases h : Sum.isLeft (moves_or x) 
  · have h1 : (moves_or x).isRight := Sum.isLeft_eq_false.mp h;
    have h2 : x∈ CompSC.{u} A := by congr;
    let f : {y : Hex A | option y x} → {y:Hex A | y∈ ⋃ p, (moves ⟨x,h2⟩) p} := 
      λ y => ⟨y.1, y.2.2⟩;
    have h3 : Function.Injective f := by 
      intro ⟨x,xh⟩ ⟨y,yh⟩ h'
      unfold f at h'
      congr
      apply Subtype.ext_iff.mp at h'
      exact h';
    exact small_of_injective (h3);
  · have h1 := Atom_no_options x h;
    exact @small_isEmpty {y : Hex A // y.option x} h1

instance small_setOf_subposition {A : Type} (x : Hex.{u} A) : Small.{u} {y : Hex A  | Subposition y x} :=
  small_transGen' _ x 

-------------------------------------------------  

lemma tempName {α : Type (u + 1)} {q : α → Prop}
(st : Player → Set (Subtype q))
(hst : st ∈ {s: Player → Set (Subtype q)|∀ p, (Small.{u} (s p) ∧ (s p).Nonempty)}) : (λ p => Set.image Subtype.val (st p)) ∈ {s: Player→Set α| ∀ p, (Small.{u} (s p) ∧ (s p).Nonempty)} := by 
  simp only [Player.forall, Set.mem_setOf_eq, Set.image_nonempty]
  simp only [Player.forall, Set.mem_setOf_eq] at hst
  let ⟨⟨a,b⟩,⟨c,d⟩⟩ := hst
  constructor
  constructor
  · exact subtype_set_small (q) (st Player.left)
  · exact b
  constructor
  · exact subtype_set_small (q) (st Player.right)
  · exact d;

-- the following is from ChatGPT (unfortunately)  
theorem acc_all {A : Type} (x : Hex A) : Acc option x := by 
  apply (QPF.Fix.ind)
  rintro val ⟨fx,rfl⟩
  cases fx with 
  | inl a =>
    constructor
    intro y h1
    rcases h1 with ⟨hcomp, hy⟩
    cases hcomp
  | inr g =>
    let ⟨st,hst⟩ := g;
    constructor
    rintro y hy
    rw [map_def] at hy
    dsimp only [option]at hy
    simp only [Set.mem_iUnion] at hy
    have hpull:  SCFunctor.map A (Subtype.val) (Sum.inr ⟨st, hst⟩) = @Sum.inr A (_) (⟨(λ p => Set.image Subtype.val (st p)),tempName st hst⟩) := by congr;
    rw [hpull] at hy
    dsimp [moves,moves_or] at hy
    simp only [QPF.Fix.dest_mk] at hy 
    rcases hy with ⟨a,b,⟨c,hc⟩,⟨dl,dr⟩⟩
    simp only at dr
    rw [dr] at hc
    exact hc

--  rw [← Sum.getRight_inr] at hg
theorem subposition_wf {A : Type} : @WellFounded (Hex A) Subposition := by
  refine ⟨fun x => Acc.transGen ?x⟩
  exact acc_all x

instance {A : Type} : IsWellFounded (Hex A) Subposition := ⟨subposition_wf⟩
instance {A : Type} : WellFoundedRelation (Hex A) := ⟨Subposition, instIsWellFoundedSubposition.wf⟩

theorem Subposition.irrefl {A : Type} (x : Hex A) : ¬Subposition x x := _root_.irrefl x

theorem option.irrefl {A : Type} (x : Hex A) : ¬option x x := by 
  apply @casesSC A (λ x => ¬x.option x)
  · intro a 
    unfold option
    simp only [Set.mem_iUnion, not_exists]
    intro ha
    have h' := Comp_nAtom_iff.mp ha
    have h'' := a.2
    contradiction
  · intro g ho 
    have h' := Subposition.irrefl g.1
    dsimp only [Subposition] at h'
    rw [Relation.transGen_iff] at h'
    simp only [not_or, not_exists, not_and] at h'
    obtain ⟨y,z⟩ := h'
    contradiction

theorem self_notMem_moves (A : Type) (p : Player) (x : CompSC A) : x.val ∉ moves x p :=  
  fun hx => Subposition.irrefl x.1 (.of_mem_moves (by 
  simp only [Set.mem_iUnion]
  use p))

/-- `WSubposition x y` is the non-strict version of `Subposition x y`. -/
@[expose]
def WSubposition {A : Type} (x y : Hex A) : Prop := x = y ∨ Subposition x y

theorem subposition_iff_exists {A : Type} {x y : Hex A} : Subposition x y ↔
   ∃ h : (y∈ CompSC A),∃ p:Player, ∃ z ∈  moves (⟨y,h⟩) p, WSubposition x z := by
   unfold WSubposition Subposition
   rw [Relation.transGen_iff]
   dsimp only [option]
   simp_rw [Set.mem_iUnion]   
   constructor
   · intro hmp
     cases hmp with
     | inl hl => 
       let ⟨a,⟨i,hi⟩⟩ := hl
       use a,i,x
       constructor
       · exact hi
       · simp only [true_or]
     | inr hr => 
       let ⟨a,⟨bl,⟨hy,⟨i,hi⟩⟩⟩⟩ := hr
       use hy,i,a
       constructor
       · exact hi
       · simp only [bl, or_true]
   · intro hmpr 
     let ⟨a,i,c,⟨d1,d2⟩⟩  := hmpr
     cases d2 with 
     | inl hl => 
       left
       use a, i
       rw [←hl] at d1
       exact d1
     | inr hr => 
       right
       use c
       constructor
       · exact hr
       · use a,i

@[simp, refl] theorem WSubposition.refl {A : Type} (x : Hex A) : WSubposition x x := .inl rfl
theorem WSubposition.rfl {A : Type} {x : Hex A} : WSubposition x x := .refl x
theorem wsubposition_of_eq {A : Type} {x y : Hex A} (hxy : x = y) : WSubposition x y := hxy ▸ .rfl

theorem wsubposition_of_subposition {A : Type} {x y : Hex A} (h : Subposition x y) :
    WSubposition x y := .inr h

alias Subposition.wsubposition := wsubposition_of_subposition

theorem subposition_of_wsubposition_of_subposition {A : Type} {x y z : Hex A}
    (hxy : WSubposition x y) (hyz : Subposition y z) : Subposition x z := by
  obtain rfl | hxy := hxy
  · exact hyz
  · exact hxy.trans hyz

theorem subposition_of_subposition_of_wsubposition {A : Type} {x y z : Hex A}
    (hxy : Subposition x y) (hyz : WSubposition y z) : Subposition x z := by
  obtain rfl | hyz := hyz
  · exact hxy
  · exact hxy.trans hyz

alias WSubposition.trans_subposition := subposition_of_wsubposition_of_subposition
alias Subposition.trans_wsubposition' := subposition_of_wsubposition_of_subposition
alias Subposition.trans_wsubposition := subposition_of_subposition_of_wsubposition
alias WSubposition.trans_subposition' := subposition_of_subposition_of_wsubposition

@[trans] theorem wsubposition_trans {A : Type} {x y z : Hex A}
    (hxy : WSubposition x y) (hyz : WSubposition y z) : WSubposition x z := by
  obtain rfl | hyz := hyz
  · exact hxy
  · exact (hxy.trans_subposition hyz).wsubposition

alias WSubposition.trans := wsubposition_trans

instance {A : Type} : @Trans (Hex A) (_) (_) Subposition Subposition Subposition := ⟨Subposition.trans⟩
instance {A : Type} : @Trans (Hex A) (_) (_) WSubposition Subposition Subposition := ⟨WSubposition.trans_subposition⟩
instance {A : Type} : @Trans (Hex A) (_) (_) Subposition WSubposition Subposition := ⟨Subposition.trans_wsubposition⟩
instance {A : Type} : @Trans (Hex A) (_) (_) WSubposition WSubposition WSubposition := ⟨WSubposition.trans⟩

theorem not_subposition_of_wsubposition {A : Type} {x y : Hex A} (hxy : WSubposition x y) :
    ¬Subposition y x := fun hyx => Subposition.irrefl x (hxy.trans_subposition hyx)

theorem not_wsubposition_of_subposition {A : Type} {x y : Hex A} (hxy : Subposition x y) :
    ¬WSubposition y x := fun hyx => Subposition.irrefl x (hxy.trans_wsubposition hyx)

alias WSubposition.not_subposition := not_subposition_of_wsubposition
alias Subposition.not_wsubposition := not_wsubposition_of_subposition

theorem wsubposition_antisymm {A : Type} {x y : Hex A}
    (hxy : WSubposition x y) (hyx : WSubposition y x) : x = y :=
  hxy.resolve_right fun h => Subposition.irrefl x (h.trans_wsubposition hyx)

alias WSubposition.antisymm := wsubposition_antisymm

theorem wsubposition_antisymm_iff {A : Type} {x y : Hex A} : x = y ↔ WSubposition x y ∧ WSubposition y x :=
  ⟨fun h => h ▸ ⟨.rfl, .rfl⟩, fun h => h.1.antisymm h.2⟩

theorem subposition_of_wsubposition_of_ne {A : Type} {x y : Hex A} (hw : WSubposition x y) (hne : x ≠ y) :
    Subposition x y := hw.resolve_left hne

theorem subposition_of_wsubposition_not_wsubposition {A : Type} {x y : Hex A}
    (hxy : WSubposition x y) (hyx : ¬WSubposition y x) : Subposition x y :=
  hxy.resolve_left fun h => hyx (wsubposition_of_eq h.symm)

theorem subposition_iff_wsubposition_not_wsubposition {A : Type} {x y : Hex A} :
    Subposition x y ↔ WSubposition x y ∧ ¬WSubposition y x :=
  ⟨fun hxy => ⟨hxy.wsubposition, hxy.not_wsubposition⟩,
    fun h => subposition_of_wsubposition_not_wsubposition h.1 h.2⟩

theorem WSubposition.of_mem_moves {A : Type} {x : Hex A} {y : CompSC A} (h : x ∈ ⋃ p, (moves.{u} y) p) :
    WSubposition x y := (Subposition.of_mem_moves h).wsubposition



end
end Hex

-- SCFunctor ()



-- def D := Unit
-- def z:Unit := Unit.unit





