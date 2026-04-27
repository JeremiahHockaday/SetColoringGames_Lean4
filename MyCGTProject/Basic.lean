-- This code is based on code by Violeta Hernández Palacios. Her work can be found here: https://github.com/vihdzp/combinatorial-games
import Mathlib.Data.Fintype.Defs
import Mathlib.Logic.Small.Set
import Mathlib.Data.Set.Image
import Mathlib.Data.Set.Basic
import MyCGTProject.SmallNonempty
import Mathlib.Data.Finset.Basic
import Init.Data.Bool
import Mathlib.Order.GameAdd
import MyCGTProject.HexFunctor

set_option linter.style.lambdaSyntax false
set_option linter.style.longLine false
set_option linter.unnecessarySeqFocus false
--set_option trace.Meta.synthInstance true

universe u



-- The following definition does not work, as it is non-positive (and lean tells us this). 
-- inductive badSetGame (α : Type u) where
-- | atom : α → badSetGame α 
-- | game : (Set (badSetGame α)) → (Set (badSetGame α))→ badSetGame α


  
-- some lemmas about stuff.



-- now we begin the QPF work


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
noncomputable def casesSC {A : Type} {α : (Hex A) → Sort*} (ha : ∀ a : AtomSC A, α a.1) (hc : ∀ g : CompSC A, α g.1) ( x : Hex A): α x := by
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
-----------------------------------------------------------------------------------

/-! ### OfSetsSC -/


/--
definition  of the `ofSetsSC` operation.
Used to implement the `!{st}` and `!{s | t}` syntax.
Here we construct a combinatorial Set Coloring game from its left and right sets. -/
noncomputable def ofSetsSC {A : Type} (st : Player → Set (Hex A)) [Small.{u} (st left)] [Nonempty (st left)] [Small.{u} (st right)] [Nonempty (st right)] : CompSC A := 
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

@[simp]
theorem ofSets_inj {A : Type} {s₁ s₂ t₁ t₂ : Set (Hex A)} [Small s₁] [Small s₂] [Small t₁] [Small t₂] [Nonempty s₁] [Nonempty s₂] [Nonempty t₁] [Nonempty t₂] :
    !{s₁ | t₁} = !{s₂ | t₂} ↔ s₁ = s₂ ∧ t₁ = t₂ := by
  simp


-- Because of the diffference between composite and atomic games, we must define subpositions very carefully.


/-- option x y : y is composite and x is in the left or right set of the game y. -/
def option {A : Type} : (Hex.{u} A) → (Hex.{u} A) → Prop := fun x y => ∃ h:y ∈ CompSC.{u} A, x ∈ ⋃ p, (moves.{u} ⟨y,h⟩) p

/-- x is a left option of the game y -/
def LOption {A : Type} : (Hex.{u} A) → (Hex.{u} A) → Prop := fun x y => ∃ h:y ∈ CompSC.{u} A, x ∈ (moves.{u} ⟨y,h⟩) left

/-- x is a right option of the game y -/
def ROption {A : Type} : (Hex.{u} A) → (Hex.{u} A) → Prop := fun x y => ∃ h:y ∈ CompSC.{u} A, x ∈ (moves.{u} ⟨y,h⟩) right

/-- x is an option of y iff x is a left or right option of y. -/
theorem option_iff_lroption {x y : Hex A} : option x y ↔ LOption x y ∨ ROption x y := by 
  dsimp [option, LOption, ROption]
  simp only [Set.mem_iUnion, Player.exists]
  constructor
  · intro ⟨h,hor⟩
    cases hor with
    | inl hl => 
      left
      use h
    | inr hr => 
      right
      use h
  · intro mpr
    cases mpr with
    | inl hl => 
      let ⟨hl,hly⟩ := hl
      use hl
      left
      exact hly
    | inr hr => 
      let ⟨hr,hry⟩ := hr
      use hr
      right
      exact hry


/-- A proper subposition of a (composite) game y is any game reachable by a nonempty sequence of left and right moves. -/
def Subposition {A : Type} : (Hex A) -> (Hex A) -> Prop := Relation.TransGen option

theorem optionSubposition {A : Type} {x y : Hex A} : option x y → Subposition x y := λ ho => by 
  unfold Subposition
  rw [Relation.transGen_iff]
  left
  exact ho

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



@[elab_as_elim]
noncomputable def sRecOn {motive : Hex A → Sort*} (x : Hex A) (ind : Π x, (Π y : Hex A, Π _ : Subposition y x, motive y) → motive x) : motive x := 
subposition_wf.recursion (_) (λ g ho => ind g ho )  

@[simp]
theorem sRecOn_eq {motive : Hex A → Sort*} (x : Hex A)
    (ind : Π x, (Π y : Hex A, Π _ : Subposition y x, motive y)→ motive x) :
    sRecOn x ind = ind x (λ y _ => sRecOn y ind) := 
    subposition_wf.fix_eq ..


@[elab_as_elim]
noncomputable def recOn {motive : Hex A → Sort*} (x : Hex A) (ind : Π x, (Π y : Hex A, Π _ : option y x, motive y) → motive x) : motive x := 
subposition_wf.recursion (x) (fun g ho => ind g (fun _ h => (ho _ (optionSubposition h))))

@[simp]
theorem recOn_eq {motive : Hex A → Sort*} (x : Hex A)
    (ind : Π x, (Π y : Hex A, Π _ : option y x, motive y)→ motive x) :
    recOn x ind = ind x (λ y _ => recOn y ind) := 
    subposition_wf.fix_eq ..


/-- Discharges proof obligations of the form `⊢ Subposition ..` arising in termination proofs
of definitions using well-founded recursion on `IGame`. -/
macro "Hex_wf" config:Lean.Parser.Tactic.optConfig : tactic =>
  `(tactic| all_goals solve_by_elim $config
    [Prod.Lex.left, Prod.Lex.right, PSigma.Lex.left, PSigma.Lex.right,
    Subposition.of_mem_moves, Subposition.trans, Subtype.prop] )


noncomputable def sum_AC (g : AtomSC A) (H : Hex.{u} B) : Hex.{u} (A×B) := 
  let motive : Hex.{u} B → Sort (u+2) := fun _ => Hex.{u} (A×B)
  let ind : Π x, (Π y : Hex B, Π _ : option y x, Hex.{u} (A×B)) → Hex.{u} (A×B) := 
  (λ x IH =>
    match val : moves_or x with 
    |Sum.inl b => 
      let g' :=(Sum.getLeft (@moves_or A g) g.2);
        (mk_atom (g',b)).val 
    |Sum.inr st => 
      have hg : Sum.isRight (moves_or x) := by
        rw [val]
        congr
      -- a subtype that bundles the data of being of type Hex B and being a subposition of x.
      let Ops := {y // y.option x}
      -- this is the image of the function that adds two smaller games together, over the set of left (resp. right) options.
      have OpsSmall : Small.{u} Ops := small_setOf_options x
      let Ops' : Player → Set (Ops) := fun p => (λ y: Ops => y.1 ∈ (st.val p))
      have ops_small : Π p:Player, Small.{u} (Ops' p) := by
        intro p
        infer_instance
      have st_nonempty : Π p:Player, Nonempty (st.val p) := fun p => by
        have :=((st.property p).right)
        simp 
        let ⟨a,b⟩ := this
        use a
      have ops_nonempty : Π p:Player, Nonempty (Ops' p):= fun p => by
        let a := Classical.choice (st_nonempty p)
        simp
        have ha : option a x := by
          
          _
          
        _
        
      let st' := λ p:Player =>  Set.image (λ y: Ops => IH y.val y.property) (λ y: Ops => y.1 ∈ (st.val p))
      have hls : Small.{u} (Set.image (λ y: Ops => IH y.val y.property) (λ y: Ops => y.1 ∈ (st.val left))):= by 
        exact small_image _ (Ops' left) 
      have hln : Nonempty (Set.image (λ y: Ops => IH y.val y.property) (λ y: Ops => y.1 ∈ (st.val left))) := 
        
        _
      have hrs : Small.{u} (Set.image (λ y: Ops => IH y.val y.property) (λ y: Ops => y.1 ∈ (st.val right))):= by        
        exact small_image _ (Ops' right) 
      have hrn : Nonempty (Set.image (λ y: Ops => IH y.val y.property) (λ y: Ops => y.1 ∈ (st.val right))) := sorry
    (@ofSetsSC (A×B) st' _ hln _ hrn).val
  )
  recOn H ind

--instance {α β} {X:Set (β)} 

-- noncomputable def SumGames {A B : Type}  (G:Hex A) (H:Hex B): Hex (A×B) :=
-- let valG := @moves_or A G;
-- let valH := @moves_or B H;
-- let aG_cH := fun (g:A) (h:Hex B) => SumGames (mk_atom g).1 h
-- let cG_aH := fun (h:B) (g: Hex A)  => SumGames  g (mk_atom h).1
-- let cG_cH := fun (g: Hex A) (h:Hex B) => SumGames g h

-- match valG, valH with
-- | Sum.inl g, Sum.inl h => (mk_atom (g,h)).1
-- | Sum.inl g, Sum.inr cH => 
--   have hl := @nonempty_range (Hex B) (Hex (A×B)) (aG_cH g) (cH.val left) (by
--                         have := (cH.property left).right
--                         simp
--                         trivial)
--   have hr := @nonempty_range (Hex B) (Hex (A×B)) (aG_cH g) (cH.val right) (by
--                         have := (cH.property right).right
--                         simp
--                         trivial)
--   let st := (fun p:Player => Set.image (aG_cH g) (cH.val p))
--   @ofSetsSC (_) st 
--     _ 
--     (by 
--     dsimp [st]
--     simp [hl])  
--     _ 
--     (by 
--      dsimp [st]
--      simp [hr])
-- --  !{L|R} 
-- | Sum.inr cG, Sum.inl h => 
--   have hl := @nonempty_range (Hex A) (Hex (A×B)) (cG_aH h) (cG.val left) (by
--                         have := (cG.property left).right
--                         simp
--                         trivial)
--   have hr := @nonempty_range (Hex A) (Hex (A×B)) (cG_aH h) (cG.val right) (by
--                         have := (cG.property right).right
--                         simp
--                         trivial)
--   let st := (fun p:Player => Set.image (cG_aH h) (cG.val p))
--   @ofSetsSC _ st 
--     _ 
--     (by 
--     dsimp [st]
--     simp [hl])  
--     _ 
--     (by 
--      dsimp [st]
--      simp [hr])
-- | Sum.inr cG, Sum.inr cH => sorry
-- termination_by (G, H) 

end Hex

-- SCFunctor ()



-- def D := Unit
-- def z:Unit := Unit.unit





