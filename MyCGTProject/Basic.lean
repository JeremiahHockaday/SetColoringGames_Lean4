-- This code is based on code by Violeta Hernández Palacios. Her work can be found here: https://github.com/vihdzp/combinatorial-games
import Mathlib.Logic.Small.Set
import Mathlib.Data.Set.Image
import Mathlib.Data.Set.Basic
import MyCGTProject.SmallNonempty
import Init.Data.Bool
import Mathlib.Order.GameAdd
import MyCGTProject.Primordial


set_option linter.style.lambdaSyntax false
set_option linter.style.longLine false
set_option linter.unnecessarySeqFocus false
--set_option trace.Meta.synthInstance true

universe u



-- The following definition does not work, as it is non-positive (and lean tells us this). 
-- inductive badSetGame (α : Type u) where
-- | atom : α → badSetGame α 
-- | game : (Set (badSetGame α)) → (Set (badSetGame α))→ badSetGame α



def Primordial (A : Type) : Type (u+1) := @QPF.Fix (PrimordialFunctor A) (QPF_PrimordialFunctor A)


noncomputable def moves_or {A : Type} : Primordial A → A ⊕ {s : (Player→ Set (Primordial A)) // ∀ p, Small.{u} (s p)} :=
  fun x =>@QPF.Fix.dest (PrimordialFunctor A) (QPF_PrimordialFunctor A) x


noncomputable def Atom (A : Type) := {x: Primordial A | Sum.isLeft (moves_or x)}
noncomputable def Comp (A : Type) := {x : Primordial A | Sum.isRight (moves_or x)}
    
noncomputable def mk_atom {A : Type} : A → Atom A := fun a => 
@Subtype.mk (Primordial A) (λ g => Sum.isLeft (moves_or g))
(@QPF.Fix.mk (PrimordialFunctor A) (QPF_PrimordialFunctor A) (@Sum.inl A {st : Player → Set (Primordial A) // ∀ p, Small (st p)} a))
 (by congr)

noncomputable def mk_comp {A : Type} (s : {st : Player → Set (Primordial A) // ∀ p, Small (st p)}) : Comp A :=
  @Subtype.mk (Primordial A) (λ g => Sum.isRight (moves_or g))
    (@QPF.Fix.mk (PrimordialFunctor A) (QPF_PrimordialFunctor A) (@Sum.inr A {st : Player → Set (Primordial A) // ∀ p, Small (st p)} s))
    (by congr)
theorem mk_moves_or_id {A : Type} (x : Primordial A) : QPF.Fix.mk (moves_or x) = x:= by 
  dsimp [moves_or]
  rw [QPF.Fix.mk_dest]


theorem mk_atom_moves_or_id {A : Type} (x : Atom A) : mk_atom (Sum.getLeft (moves_or x.1) x.2) = x := by 
  unfold mk_atom
  congr
  rw [Sum.inl_getLeft, mk_moves_or_id]

theorem mk_comp_moves_or_id {A : Type} (x : Comp A) : mk_comp (Sum.getRight (moves_or x.1) x.2) = x := by 
  unfold mk_comp
  congr
  rw [Sum.inr_getRight, mk_moves_or_id]


theorem moves_or_mk_comp_id {A : Type} (st : Player → Set (Primordial A)) (h : ∀ p, Small (st p)) : moves_or (mk_comp ⟨st, h⟩) = Sum.inr ⟨st, h⟩ := by 
  dsimp [moves_or,mk_comp]
  rw [QPF.Fix.dest_mk] 


theorem moves_or_mk_atom_id {A : Type} (x : A) : moves_or (mk_atom x) = Sum.inl x
:= by 
  dsimp [moves_or,mk_atom]
  rw [QPF.Fix.dest_mk] 

-- Special Games
noncomputable def casesSC {A : Type} {α : (Primordial A) → Sort*} (ha : ∀ a : Atom A, α a.1) (hc : ∀ g : Comp A, α g.1) ( x : Primordial A): α x := by
  cases h : Sum.isRight (moves_or x)
  ·have h1 : (moves_or x).isLeft := Sum.isRight_eq_false.mp h;
   exact (ha ⟨x,h1⟩)
  ·exact (hc ⟨x,h⟩)

theorem Atom_nComp_iff {A : Type} {x : Primordial A} : x∈ Atom A ↔ x ∉Comp A := by
  dsimp [Comp] 
  dsimp [Atom]
  constructor
  · intro ha
    simp only [Bool.not_eq_true, Sum.isRight_eq_false]
    exact ha
  · intro nhc
    simp only [Bool.not_eq_true, Sum.isRight_eq_false] at nhc
    exact nhc
theorem Comp_nAtom_iff {A : Type} {x : Primordial A} : x∈ Comp A ↔ x ∉Atom A := by
  dsimp [Comp]
  dsimp [Atom]
  constructor
  · intro nhc
    simp only [Bool.not_eq_true, Sum.isLeft_eq_false]
    exact nhc
  · intro ha
    simp only [Bool.not_eq_true, Sum.isLeft_eq_false] at ha
    exact ha


namespace Primordial
export Player (left right)
-----------------------------------------------------------------------------------

/-! ### OfSetsPrimordial -/


/--
definition  of the `ofSets` operation.
Used to implement the `!{st}` and `!{s | t}` syntax.
Here we construct a combinatorial Set Coloring game from its left and right sets. -/
noncomputable def ofSets {A : Type} (st : Player → Set (Primordial A)) [Small.{u} (st left)] [Small.{u} (st right)] : Comp A := 
    @Subtype.mk (Primordial A) (λ x => Sum.isRight (moves_or x)) (@mk_comp A ⟨st , 
      λ p => match p with
        |left => by assumption
        |right => by assumption⟩)
    (by congr)
    

@[inherit_doc Primordial.ofSets]
macro "!{" st:term:max "}"  : term => `(Primordial.ofSets $st)

@[inherit_doc Primordial.ofSets]
macro "!{" s:term " | " t:term "}" : term => `(!{(Player.cases $s $t)})


recommended_spelling "ofSets" for "!{st}" in [Primordial.ofSets, «term!{_}»]
recommended_spelling "ofSets" for "!{s | t}" in [Primordial.ofSets, «term!{_|_}»]

open Lean PrettyPrinter Delaborator SubExpr in
/-- Delaborates `ofSets (Player.cases s t)` to `!{s | t}` and `ofSets st` to `!{st}`. -/
@[app_delab Primordial.ofSets]
meta def delabOfSetsSC : Delab := do
  let e ← getExpr
  guard <| e.isAppOfArity' ``Primordial.ofSets 7
  withNaryArg 3 do
    let e ← getExpr
    if e.isAppOfArity' ``Player.cases 3 then
      let s ← withNaryArg 1 delab
      let t ← withNaryArg 2 delab
      `(!{$s | $t})
    else
      let st ← delab
      `(!{$st})
 
theorem ofSets_eq_ofSets_cases {A : Type} (st : Player → Set (Primordial.{u} A)) [Small.{u} (st left)] [Small.{u} (st right)] :
    !{st} = !{(st left) | (st right)} := by
    congr; ext1 p; cases p <;> rfl


/-- The set of moves of a composite game. -/
def moves {A : Type} (x : Comp A) (p : Player) : Set (Primordial A) :=  
  (@Sum.getRight A {st : Player → Set (Primordial A) // ∀ p, Small (st p)} (moves_or x.1) x.2).1 p

/-- The set of left moves of a composite game. -/
notation x:max "ᴸ" => moves x left 

/-- The set of right moves of a composite game. -/
notation x:max "ᴿ" => moves x right 

instance small_moves {A : Type} (p : Player) (x : Comp.{u} A) : Small.{u} (moves x p) := 
  let g:= Sum.getRight (moves_or x.1) x.2; 
  have he : g.1 p = moves x p := by rfl;
  let hg := (g.2 p);
  by 
  rw [he] at hg 
  exact hg;



@[simp]
theorem moves_ofSets {A : Type} (st : Player → Set (Primordial A)) (p : Player) [Small.{u} (st left)] [Small.{u} (st right)] :
   moves !{st} p = st p := by 
  dsimp [ofSets, moves]  
  simp [moves_or_mk_comp_id]


@[simp]
theorem ofSets_moves {A : Type} (x : Comp A) : !{(moves x)}  = x := by
  dsimp [ ofSets]
  unfold moves
  rw [Subtype.eta] 
  rw [mk_comp_moves_or_id]

theorem leftMoves_ofSets (s t : Set (Primordial A)) [Small.{u} s] [Small.{u} t] : !{s|t}ᴸ = s :=  
moves_ofSets ..

theorem rightMoves_ofSets (s t : Set (Primordial A)) [Small.{u} s] [Small.{u} t] : !{s|t}ᴿ = t :=  
moves_ofSets ..

@[simp]
theorem ofSets_leftMoves_rightMoves (x : Comp A) : !{xᴸ | xᴿ} = x :=  by 
  convert (ofSets_moves x) with p
  funext p
  cases p <;> dsimp [Player.cases]

@[ext]
theorem ext {A : Type} {x y : Comp A} (h : ∀ p, moves x p = moves y p) : x = y :=  by 
    rw [← ofSets_moves x , ← ofSets_moves y ]
    simp_rw [funext h] 
    
       
@[simp]
theorem ofSets_inj' {A : Type} {st₁ st₂ : Player → Set (Primordial A)}
    [Small (st₁ left)] [Small (st₁ right)] [Small (st₂ left)] [Small (st₂ right)] :
    !{st₁} =!{st₂}↔ st₁ = st₂ := by
    simp_rw [Primordial.ext_iff, moves_ofSets, funext_iff]

@[simp]
theorem ofSets_inj {A : Type} {s₁ s₂ t₁ t₂ : Set (Primordial A)} [Small s₁] [Small s₂] [Small t₁] [Small t₂] :
    !{s₁ | t₁} = !{s₂ | t₂} ↔ s₁ = s₂ ∧ t₁ = t₂ := by
  simp


-- Because of the diffference between composite and atomic games, we must define subpositions very carefully.


/-- option x y : y is composite and x is in the left or right set of the game y. -/
def option {A : Type} : (Primordial.{u} A) → (Primordial.{u} A) → Prop := fun x y => ∃ h:y ∈ Comp.{u} A, x ∈ ⋃ p, (moves.{u} ⟨y,h⟩) p

/-- x is a left option of the game y -/
def LOption {A : Type} : (Primordial.{u} A) → (Primordial.{u} A) → Prop := fun x y => ∃ h:y ∈ Comp.{u} A, x ∈ (moves.{u} ⟨y,h⟩) left

/-- x is a right option of the game y -/
def ROption {A : Type} : (Primordial.{u} A) → (Primordial.{u} A) → Prop := fun x y => ∃ h:y ∈ Comp.{u} A, x ∈ (moves.{u} ⟨y,h⟩) right

/-- x is an option of y iff x is a left or right option of y. -/
theorem option_iff_lroption {x y : Primordial A} : option x y ↔ LOption x y ∨ ROption x y := by 
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
def Subposition {A : Type} : (Primordial A) -> (Primordial A) -> Prop := Relation.TransGen option

theorem optionSubposition {A : Type} {x y : Primordial A} : option x y → Subposition x y := λ ho => by 
  unfold Subposition
  rw [Relation.transGen_iff]
  left
  exact ho

@[aesop unsafe apply 50%]
theorem Subposition.of_mem_moves {A : Type} {x : Primordial A} {y : Comp A} (h : x ∈ ⋃ p, (moves.{u} y) p) : Subposition x y.1 :=
  Relation.TransGen.single (by 
    unfold option
    have h':y.1∈ Comp A := by 
      simp
    use h')

/-- transitivity of Subposition relation -/
theorem Subposition.trans {A : Type} {a b c : Primordial A} : Subposition a b → Subposition b c -> Subposition a c := Relation.TransGen.trans

instance {A : Type} : IsTrans (Primordial A) Subposition := inferInstanceAs (IsTrans _ (Relation.TransGen _))
  

instance comp.small_setOf_options {A : Type} : 
∀ x : (Comp.{u} A),  Small.{u , u + 1} {y : Primordial A | y ∈ ⋃ p, (moves x) p} := 
  λ x =>
  have h1 : Small.{u} (⋃ p, (moves x) p) := by infer_instance;
  let f : {y : Primordial A | y ∈ ⋃ p, (moves x) p} → ⋃ p, (moves x) p := λ x => x;
  let g : ⋃ p, (moves x) p→{y : Primordial A | y ∈ ⋃ p, (moves x) p} := λ x => x;
  have h3 : g∘f = id := by congr;
  have h4 : Function.LeftInverse g f := by 
    dsimp [Function.LeftInverse]
    intro x
    congr;
  small_of_injective (Function.LeftInverse.injective h4)

instance Atom_no_options {A : Type} (x : Primordial.{u} A) (h : Sum.isLeft (moves_or x)) : IsEmpty {y : Primordial A // y.option x}:=
have h1 := Sum.isRight_eq_false.mpr h;
    have h2 : x ∉ Comp.{u} A  := by 
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
    have h3 : ∀ y : {y : Primordial A | option y x}, False := by 
      intro ⟨y,a⟩
      apply Exists.nonempty at a;
      apply (@nonempty_prop (x ∈ Comp A)).mp at a;
      contradiction;
    by exact (isEmpty_iff.mpr h3)

instance small_setOf_options {A : Type} : ∀ x : (Primordial.{u} A),  Small.{u , u + 1} {y : Primordial A // y.option x} := λ x => by 
  dsimp [option]
  cases h : Sum.isLeft (moves_or x) 
  · have h1 : (moves_or x).isRight := Sum.isLeft_eq_false.mp h;
    have h2 : x∈ Comp.{u} A := by congr;
    let f : {y : Primordial A | option y x} → {y:Primordial A | y∈ ⋃ p, (moves ⟨x,h2⟩) p} := 
      λ y => ⟨y.1, y.2.2⟩;
    have h3 : Function.Injective f := by 
      intro ⟨x,xh⟩ ⟨y,yh⟩ h'
      unfold f at h'
      congr
      apply Subtype.ext_iff.mp at h'
      exact h';
    exact small_of_injective (h3);
  · have h1 := Atom_no_options x h;
    exact @small_isEmpty {y : Primordial A // y.option x} h1

instance small_setOf_subposition {A : Type} (x : Primordial.{u} A) : Small.{u} {y : Primordial A  | Subposition y x} :=
  small_transGen' _ x 

-- -------------------------------------------------  

lemma tempName {α : Type (u + 1)} {q : α → Prop}
(st : Player → Set (Subtype q))
(hst : st ∈ {s: Player → Set (Subtype q)|∀ p, Small.{u} (s p)}) : (λ p => Set.image Subtype.val (st p)) ∈ {s: Player→Set α| ∀ p, Small.{u} (s p)} := by 
  simp only [Player.forall, Set.mem_setOf_eq]
  simp only [Player.forall, Set.mem_setOf_eq] at hst
  let ⟨b,d⟩ := hst
  constructor
  · exact subtype_set_small (q) (st Player.left)
  · exact subtype_set_small (q) (st Player.right)

theorem acc_all {A : Type} (x : Primordial A) : Acc option x := by 
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
    rw [PrimordialFunctor.map_def] at hy
    dsimp only [option]at hy
    simp only [Set.mem_iUnion] at hy
    have hpull:  PrimordialFunctor.map A (Subtype.val) (Sum.inr ⟨st, hst⟩) = @Sum.inr A (_) (⟨(λ p => Set.image Subtype.val (st p)),tempName st hst⟩) := by congr;
    rw [hpull] at hy
    dsimp [moves,moves_or] at hy
    simp only [QPF.Fix.dest_mk] at hy 
    rcases hy with ⟨a,b,⟨c,hc⟩,⟨dl,dr⟩⟩
    simp only at dr
    rw [dr] at hc
    exact hc


theorem subposition_wf {A : Type} : @WellFounded (Primordial A) Subposition := by
  refine ⟨fun x => Acc.transGen ?x⟩
  exact acc_all x

instance {A : Type} : IsWellFounded (Primordial A) Subposition := ⟨subposition_wf⟩
instance {A : Type} : WellFoundedRelation (Primordial A) := ⟨Subposition, instIsWellFoundedSubposition.wf⟩

theorem Subposition.irrefl {A : Type} (x : Primordial A) : ¬Subposition x x := _root_.irrefl x

theorem option.irrefl {A : Type} (x : Primordial A) : ¬option x x := by 
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

theorem self_notMem_moves (A : Type) (p : Player) (x : Comp A) : x.val ∉ moves x p :=  
  fun hx => Subposition.irrefl x.1 (.of_mem_moves (by 
  simp only [Set.mem_iUnion]
  use p))

/-- `WSubposition x y` is the non-strict version of `Subposition x y`. -/
@[expose]
def WSubposition {A : Type} (x y : Primordial A) : Prop := x = y ∨ Subposition x y

theorem subposition_iff_exists {A : Type} {x y : Primordial A} : Subposition x y ↔
   ∃ h : (y∈ Comp A),∃ p:Player, ∃ z ∈  moves (⟨y,h⟩) p, WSubposition x z := by
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

@[simp, refl] theorem WSubposition.refl {A : Type} (x : Primordial A) : WSubposition x x := .inl rfl
theorem WSubposition.rfl {A : Type} {x : Primordial A} : WSubposition x x := .refl x
theorem wsubposition_of_eq {A : Type} {x y : Primordial A} (hxy : x = y) : WSubposition x y := hxy ▸ .rfl

theorem wsubposition_of_subposition {A : Type} {x y : Primordial A} (h : Subposition x y) :
    WSubposition x y := .inr h

alias Subposition.wsubposition := wsubposition_of_subposition

theorem subposition_of_wsubposition_of_subposition {A : Type} {x y z : Primordial A}
    (hxy : WSubposition x y) (hyz : Subposition y z) : Subposition x z := by
  obtain rfl | hxy := hxy
  · exact hyz
  · exact hxy.trans hyz

theorem subposition_of_subposition_of_wsubposition {A : Type} {x y z : Primordial A}
    (hxy : Subposition x y) (hyz : WSubposition y z) : Subposition x z := by
  obtain rfl | hyz := hyz
  · exact hxy
  · exact hxy.trans hyz

alias WSubposition.trans_subposition := subposition_of_wsubposition_of_subposition
alias Subposition.trans_wsubposition' := subposition_of_wsubposition_of_subposition
alias Subposition.trans_wsubposition := subposition_of_subposition_of_wsubposition
alias WSubposition.trans_subposition' := subposition_of_subposition_of_wsubposition

@[trans] theorem wsubposition_trans {A : Type} {x y z : Primordial A}
    (hxy : WSubposition x y) (hyz : WSubposition y z) : WSubposition x z := by
  obtain rfl | hyz := hyz
  · exact hxy
  · exact (hxy.trans_subposition hyz).wsubposition

alias WSubposition.trans := wsubposition_trans

instance {A : Type} : @Trans (Primordial A) (_) (_) Subposition Subposition Subposition := ⟨Subposition.trans⟩
instance {A : Type} : @Trans (Primordial A) (_) (_) WSubposition Subposition Subposition := ⟨WSubposition.trans_subposition⟩
instance {A : Type} : @Trans (Primordial A) (_) (_) Subposition WSubposition Subposition := ⟨Subposition.trans_wsubposition⟩
instance {A : Type} : @Trans (Primordial A) (_) (_) WSubposition WSubposition WSubposition := ⟨WSubposition.trans⟩

theorem not_subposition_of_wsubposition {A : Type} {x y : Primordial A} (hxy : WSubposition x y) :
    ¬Subposition y x := fun hyx => Subposition.irrefl x (hxy.trans_subposition hyx)

theorem not_wsubposition_of_subposition {A : Type} {x y : Primordial A} (hxy : Subposition x y) :
    ¬WSubposition y x := fun hyx => Subposition.irrefl x (hxy.trans_wsubposition hyx)

alias WSubposition.not_subposition := not_subposition_of_wsubposition
alias Subposition.not_wsubposition := not_wsubposition_of_subposition

theorem wsubposition_antisymm {A : Type} {x y : Primordial A}
    (hxy : WSubposition x y) (hyx : WSubposition y x) : x = y :=
  hxy.resolve_right fun h => Subposition.irrefl x (h.trans_wsubposition hyx)

alias WSubposition.antisymm := wsubposition_antisymm

theorem wsubposition_antisymm_iff {A : Type} {x y : Primordial A} : x = y ↔ WSubposition x y ∧ WSubposition y x :=
  ⟨fun h => h ▸ ⟨.rfl, .rfl⟩, fun h => h.1.antisymm h.2⟩

theorem subposition_of_wsubposition_of_ne {A : Type} {x y : Primordial A} (hw : WSubposition x y) (hne : x ≠ y) :
    Subposition x y := hw.resolve_left hne

theorem subposition_of_wsubposition_not_wsubposition {A : Type} {x y : Primordial A}
    (hxy : WSubposition x y) (hyx : ¬WSubposition y x) : Subposition x y :=
  hxy.resolve_left fun h => hyx (wsubposition_of_eq h.symm)

theorem subposition_iff_wsubposition_not_wsubposition {A : Type} {x y : Primordial A} :
    Subposition x y ↔ WSubposition x y ∧ ¬WSubposition y x :=
  ⟨fun hxy => ⟨hxy.wsubposition, hxy.not_wsubposition⟩,
    fun h => subposition_of_wsubposition_not_wsubposition h.1 h.2⟩

theorem WSubposition.of_mem_moves {A : Type} {x : Primordial A} {y : Comp A} (h : x ∈ ⋃ p, (moves.{u} y) p) :
    WSubposition x y := (Subposition.of_mem_moves h).wsubposition



@[elab_as_elim]
noncomputable def sRecOn {motive : Primordial A → Sort*} (x : Primordial A) (ind : Π x, (Π y : Primordial A, Π _ : Subposition y x, motive y) → motive x) : motive x := 
subposition_wf.recursion (_) (λ g ho => ind g ho )  

@[simp]
theorem sRecOn_eq {motive : Primordial A → Sort*} (x : Primordial A)
    (ind : Π x, (Π y : Primordial A, Π _ : Subposition y x, motive y)→ motive x) :
    sRecOn x ind = ind x (λ y _ => sRecOn y ind) := 
    subposition_wf.fix_eq ..

/-- How to use:
--- To define a function/theorem, define something with the same type as ind. -/
@[elab_as_elim]
noncomputable def recOn {motive : Primordial A → Sort*} (x : Primordial A) (ind : Π x, (Π y : Primordial A, Π _ : option y x, motive y) → motive x) : motive x := 
subposition_wf.recursion (x) (fun g ho => ind g (fun _ h => (ho _ (optionSubposition h))))

@[simp]
theorem recOn_eq {motive : Primordial A → Sort*} (x : Primordial A)
    (ind : Π x, (Π y : Primordial A, Π _ : option y x, motive y)→ motive x) :
    recOn x ind = ind x (λ y _ => recOn y ind) := 
    subposition_wf.fix_eq ..


/-- Discharges proof obligations of the form `⊢ Subposition ..` arising in termination proofs
of definitions using well-founded recursion on `IGame`. -/
macro "Primordial_wf" config:Lean.Parser.Tactic.optConfig : tactic =>
  `(tactic| all_goals solve_by_elim $config
    [Prod.Lex.left, Prod.Lex.right, PSigma.Lex.left, PSigma.Lex.right,
    Subposition.of_mem_moves, Subposition.trans, Subtype.prop] )



/-- Given a function f: A→ B and a game G:Primordial A returns a game of type Primordial B, the result of applying the map -/
noncomputable def MAP {A B : Type} (f : A → B) : Primordial.{u} A → Primordial.{u} B := 
  let motive : Primordial.{u} A -> Sort (u+2) := λ _ => Primordial.{u} B
  let ind : Π x, (Π y : Primordial A, Π _ : Subposition y x, Primordial.{u} B) → Primordial.{u} B :=
    (λ x IH =>
    match val : @moves_or A x with
    | Sum.inl a => 
      mk_atom (f a)
    | Sum.inr st =>       
      let Ops := {y // y.Subposition x}
      -- this is the image of the function that adds two smaller games together, over the set of left (resp. right) options.
      have smallOps : Small.{u} Ops := small_setOf_subposition x
      -- st' is the sum of these two games, defined inductively.
      let st' := λ p:Player =>  Set.image (λ y: Ops => IH y.val y.property) (λ y: Ops => y.1 ∈ (st.val p))
      --- proofs of smallness
      have hl : Small.{u} (Set.image (λ y: Ops => IH y.val y.property) (λ y: Ops => y.1 ∈ (st.val left))):= by 
        have l_small := (st.property left)
        let X : Set (Ops) := (λ y: Ops => y.1 ∈ (st.val left))
        have : Small.{u} X := by infer_instance
        infer_instance
      have hr : Small.{u} (Set.image (λ y: Ops => IH y.val y.property) (λ y: Ops => y.1 ∈ (st.val right))):= by
        have l_small := (st.property right)
        let X : Set (Ops) := (λ y: Ops => y.1 ∈ (st.val right))
        have : Small.{u} X := by infer_instance
        infer_instance
    -- This is the value that should be returned
    (@ofSets B st' hl hr).val
    )
  (λ G => sRecOn G ind)

/-- Want to define a new definition that straight up uses recursion -/
noncomputable def MAP' (f : A → B) : Primordial A → Primordial B := fun x =>
  match val : moves_or x with
  | Sum.inl a => 
      mk_atom (f a)
  | Sum.inr st => sorry


noncomputable def sum_AA : Atom A→ Atom B → Atom (A×B) := λ a b => 
let a' :=(Sum.getLeft (@moves_or A a) a.2);
let b' :=(Sum.getLeft (@moves_or B b) b.2);
(mk_atom (a',b'))


noncomputable def sum_AC (g : Atom A) (H : Primordial.{u} B) : Primordial.{u} (A×B) := 
  let g' :A := (Sum.getLeft (@moves_or A g) g.2)
  let f := (λ b:B => (g',b))
  MAP f H
  
  
instance ProductAssoc {A B C : Type} : ((A×B)×C)≃(A×(B×C)):= 
  let f :((A×B)×C)→(A×(B×C)) := fun ((x1,x2),x3) => (x1,(x2,x3))
  let g :(A×(B×C))→((A×B)×C) := fun (x1,(x2,x3)) => ((x1,x2),x3)
  have hfg : f∘ g = id := by
    congr
  have hgf :  g∘f = id := by
    congr 
  ⟨f, g, 
    by
      unfold Function.LeftInverse
      apply funext_iff.mp at hgf
      simp only[Function.comp_apply] at hgf
      exact hgf,
     by
      unfold Function.RightInverse
      apply funext_iff.mp at hfg
      simp only[Function.comp_apply] at hfg
      exact hfg⟩


example {A B C : Type} {a : Atom A} {b : Atom B} {c : Primordial C} : 
Primordial.MAP ProductAssoc.toFun (sum_AC (sum_AA a b) c) = sum_AC a (sum_AC b c) := sorry

end Primordial

-- PrimordialFunctor ()



-- def D := Unit
-- def z:Unit := Unit.unit





