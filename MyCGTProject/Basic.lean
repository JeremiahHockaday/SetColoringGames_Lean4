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

noncomputable abbrev IsAtom {A : Type} (x : Primordial A):= Sum.isLeft (moves_or x)

noncomputable abbrev IsComp {A : Type} (x : Primordial A) := Sum.isRight (moves_or x)

noncomputable def Atom (A : Type) := {x: Primordial A | IsAtom x}
noncomputable def Comp (A : Type) := {x : Primordial A | IsComp x}
    
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

@[simp]
theorem mk_comp_moves_or_id {A : Type} (x : Comp A) : mk_comp (Sum.getRight (moves_or x.1) x.2) = x := by 
  unfold mk_comp
  congr
  rw [Sum.inr_getRight, mk_moves_or_id]

@[simp]
theorem moves_or_mk_comp_id {A : Type} (st : Player → Set (Primordial A)) (h : ∀ p, Small (st p)) : moves_or (mk_comp ⟨st, h⟩) = Sum.inr ⟨st, h⟩ := by 
  dsimp [moves_or,mk_comp]
  rw [QPF.Fix.dest_mk] 


@[simp]
theorem moves_or_mk_atom_id {A : Type} (x : A) : moves_or (mk_atom x) = Sum.inl x
:= by 
  dsimp [moves_or,mk_atom]
  rw [QPF.Fix.dest_mk] 

-- Special Games
noncomputable def casesSC {A : Type} {α : (Primordial A) → Sort*} (x : Primordial A) (ha : ∀ a : Atom A, α a.1) (hc : ∀ g : Comp A, α g.1) : α x := by
  cases h : Sum.isRight (moves_or x)
  ·have h1 : (moves_or x).isLeft := Sum.isRight_eq_false.mp h;
   exact (ha ⟨x,h1⟩)
  ·exact (hc ⟨x,h⟩)

noncomputable def casesSC' {A : Type} {α : (Primordial A) → Sort*} (x : Primordial A) (ha : ∀ a :A, α (mk_atom a)) (hc : ∀ G : {st : Player → Set (Primordial A) // ∀ p, Small (st p)}, α (mk_comp G)) : α x := by
  cases h : IsComp x
  · have this := ha (Sum.getLeft (moves_or x) (Sum.isRight_eq_false.mp h))
    dsimp [mk_atom, moves_or] at this
    simp only [Sum.inl_getLeft, QPF.Fix.mk_dest] at this
    exact this
  · have this := hc (Sum.getRight (moves_or x) (h))
    dsimp [mk_comp, moves_or] at this
    simp only [Sum.inr_getRight, QPF.Fix.mk_dest] at this
    exact this


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
@[no_expose]
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
def moves {A : Type} (x : Primordial A) (p : Player) : Set (Primordial A) :=  
  if h: IsComp x then (@Sum.getRight A {st : Player → Set (Primordial A) // ∀ p, Small (st p)} (moves_or x) h).1 p
  else ∅

lemma moves_comp {A : Type} (x : Primordial A) (h : IsComp x) (p : Player) : moves x p = (@Sum.getRight A {st : Player → Set (Primordial A) // ∀ p, Small (st p)} (moves_or x) h).1 p := by
   dsimp [moves]
   simp [h]

/-- The set of left moves of a composite game. -/
notation x:max "ᴸ" => moves x left 

/-- The set of right moves of a composite game. -/
notation x:max "ᴿ" => moves x right 

instance small_moves {A : Type} (p : Player) (x : Primordial.{u} A) : Small.{u} (moves x p) :=
  match h:IsComp x with
  |true =>
  let g:= Sum.getRight (moves_or x) h; 
  have he : g.1 p = moves x p := by
    dsimp [moves]
    simp only [h]
    rfl;
  let hg := (g.2 p);
  by 
    rw [he] at hg 
    exact hg;
  |false =>by
   dsimp [moves]
   simp only [h, Bool.false_eq_true, ↓reduceDIte]
   infer_instance


  



@[simp]
theorem moves_ofSets {A : Type} (st : Player → Set (Primordial A)) (p : Player) [Small.{u} (st left)] [Small.{u} (st right)] :
   moves !{st}.1 p = st p := by 
  dsimp [ofSets, moves]  
  simp [moves_or_mk_comp_id]


@[simp]
theorem ofSets_moves {A : Type} (x : Primordial A) (h : IsComp x) : !{(moves x)}  = ⟨x,h⟩  := by
  dsimp [ ofSets]
  unfold moves
  simp [h]
  dsimp [mk_comp,moves_or]
  simp [QPF.Fix.mk_dest]
  congr

--@[game_cmp]
theorem leftMoves_ofSets (s t : Set (Primordial A)) [Small.{u} s] [Small.{u} t] : !{s|t}ᴸ = s :=  
moves_ofSets ..

--@[game_cmp]
theorem rightMoves_ofSets (s t : Set (Primordial A)) [Small.{u} s] [Small.{u} t] : !{s|t}ᴿ = t :=  
moves_ofSets ..

@[simp]
theorem ofSets_leftMoves_rightMoves (x : Primordial A) (h : IsComp x) : !{xᴸ | xᴿ} = ⟨x,h⟩ :=  by 
  convert (ofSets_moves x h) with p
  funext p
  cases p <;> dsimp [Player.cases]

@[ext]
theorem ext {A : Type} (x y : Comp A) (hxy : ∀ p, moves x.val p = moves y.val p) : x = y :=  by
    have hx : IsComp x.1 := by use x.2 
    have hy : IsComp y.1 := by use y.2
    have thisx : x= ⟨x.1,hx⟩ := by simp
    have thisy : y= ⟨y.1,hy⟩ := by simp
    rw [thisx, thisy]
    rw [← ofSets_moves x.1 hx  , ← ofSets_moves y.1 hy ]
    simp_rw [funext hxy]


theorem ofSets_inj' {A : Type} {st₁ st₂ : Player → Set (Primordial A)}
    [Small (st₁ left)] [Small (st₁ right)] [Small (st₂ left)] [Small (st₂ right)] :
    !{st₁} =!{st₂}↔ st₁ = st₂ := by
    simp_rw [Primordial.ext_iff, moves_ofSets, funext_iff]

theorem ofSets_inj {A : Type} {s₁ s₂ t₁ t₂ : Set (Primordial A)} [Small s₁] [Small s₂] [Small t₁] [Small t₂] :
    !{s₁ | t₁} = !{s₂ | t₂} ↔ s₁ = s₂ ∧ t₁ = t₂ := by
      have this: Player.cases s₁ t₁ =Player.cases s₂ t₂ ↔ s₁ = s₂ ∧ t₁ =t₂ := by
        simp
      have this2 : ofSets (Player.cases s₁ t₁) = ofSets (Player.cases s₂ t₂) ↔ Player.cases s₁ t₁  = Player.cases s₂ t₂ := by
        constructor
        · intro h
          have h' :  moves (ofSets (Player.cases s₁ t₁)).1 = moves (ofSets (Player.cases s₂ t₂)).1 := by
            apply (congrArg)
            simp [h]
          have h'' : ∀ p:Player, moves (ofSets (Player.cases s₁ t₁)).1 p = moves (ofSets (Player.cases s₂ t₂)).1 p := by
           intro p
           simp only [h']
          funext p
          simp only [← moves_ofSets (Player.cases s₁ t₁) p,← moves_ofSets (Player.cases s₂ t₂) p]
          exact h'' p
        · intro h
          simp [h]
      simp [this2,this]
        


-- Because of the diffference between composite and atomic games, we must define subpositions very carefully.


/-- option x y : y is composite and x is in the left or right set of the game y. -/
def option {A : Type} : (Primordial.{u} A) → (Primordial.{u} A) → Prop := fun x y =>  x ∈ ⋃ p, (moves.{u} y) p

/-- x is a left option of the game y -/
def LOption {A : Type} : (Primordial.{u} A) → (Primordial.{u} A) → Prop := fun x y => x ∈ (moves.{u} y) left

/-- x is a right option of the game y -/
def ROption {A : Type} : (Primordial.{u} A) → (Primordial.{u} A) → Prop := fun x y => x ∈ (moves.{u} y) right

/-- x is an option of y iff x is a left or right option of y. -/
theorem option_iff_lroption {x y : Primordial A} : option x y ↔ LOption x y ∨ ROption x y := by 
  dsimp [option, LOption, ROption]
  simp only [Set.mem_iUnion, Player.exists]
  

/-- A proper subposition of a (composite) game y is any game reachable by a nonempty sequence of left and right moves. -/
def Subposition {A : Type} : (Primordial A) -> (Primordial A) -> Prop := Relation.TransGen option

theorem optionSubposition {A : Type} {x y : Primordial A} : option x y → Subposition x y := λ ho => by 
  unfold Subposition
  rw [Relation.transGen_iff]
  left
  exact ho

@[aesop unsafe apply 50%]
theorem Subposition.of_mem_moves {A : Type} {x y : Primordial A} (h : x ∈ ⋃ p, (moves.{u} y) p) : Subposition x y :=
  Relation.TransGen.single (h)

/-- transitivity of Subposition relation -/
theorem Subposition.trans {A : Type} {a b c : Primordial A} : Subposition a b → Subposition b c -> Subposition a c := Relation.TransGen.trans

instance {A : Type} : IsTrans (Primordial A) Subposition := inferInstanceAs (IsTrans _ (Relation.TransGen _))
  

instance comp.small_setOf_options {A : Type} : 
∀ x : (Primordial.{u} A),  Small.{u , u + 1} {y : Primordial A | y ∈ ⋃ p, (moves x) p} := 
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

instance Atom_no_options {A : Type} (x : Primordial.{u} A) (h : IsAtom x) : IsEmpty {y : Primordial A // y.option x}:=
    have h1: ¬IsComp x := Sum.not_isRight.mpr h;
    have h3 : ∀ y : {y : Primordial.{u} A | option y x}, False := by 
      intro ⟨y,a⟩
      dsimp [option,moves] at a
      simp only [h1, Bool.false_eq_true, ↓reduceDIte, Set.iUnion_empty] at a
      contradiction
    by simp only [(@isEmpty_iff {y:Primordial.{u} A // option y x}).mpr h3]
    
     

instance small_setOf_options {A : Type} : ∀ x : (Primordial.{u} A),  Small.{u , u + 1} {y : Primordial A // y.option x} := λ x => by 
  cases h : IsAtom x 
  · have h1 : IsComp x := Sum.isLeft_eq_false.mp h;
    let f : {y : Primordial A | option y x} → {y:Primordial A | y∈ ⋃ p, (moves x) p} := 
      λ y => ⟨y.1, y.2⟩;
    have h3 : Function.Injective f := by 
      intro ⟨x,xh⟩ ⟨y,yh⟩ h'
      unfold f at h'
      congr
      apply Subtype.ext_iff.mp at h'
      exact h';
    exact small_of_injective (h3);
  · have h1 := Atom_no_options x h;
    simp only [@small_isEmpty {y : Primordial A // y.option x} h1]
    

instance small_setOf_subposition {A : Type} (x : Primordial.{u} A) : Small.{u} {y : Primordial A  | Subposition y x} :=
  small_transGen' _ x 

-- -------------------------------------------------  

lemma tempName {α : Type (u + 1)} {q : α → Prop}
(st : Player → Set (Subtype q))
(hst : st ∈ {s: Player → Set (Subtype q)|∀ p, Small.{u} (s p)}) : (λ p => Set.image Subtype.val (st p)) ∈ {s: Player→Set α| ∀ p, Small.{u} (s p)} := by 
  simp only [Player.forall, Set.mem_setOf_eq]
  simp only [Player.forall, Set.mem_setOf_eq] at hst
  let ⟨_,_⟩ := hst
  constructor
  · exact subtype_set_small (q) (st Player.left)
  · exact subtype_set_small (q) (st Player.right)

theorem acc_all {A : Type} (x : Primordial A) : Acc option x := by 
  apply (QPF.Fix.ind)
  rintro val ⟨fx,rfl⟩
  cases fx with 
  | inl a =>
      constructor
      -- contradiction: atoms have no options
      have : IsAtom (QPF.Fix.mk (@PrimordialFunctor.map A (Subtype (Acc option)) _ Subtype.val (Sum.inl a))) := by
       simp [IsAtom, moves_or, QPF.Fix.dest_mk]
       congr
      have := (Atom_no_options _ this)
      rintro y hy
      rw [isEmpty_iff] at this
      exfalso
      exact this ⟨y,hy⟩
    
  | inr g =>
    let ⟨st,hst⟩ := g;
    have hcomp : IsComp (QPF.Fix.mk (PrimordialFunctor.map A Subtype.val (Sum.inr ⟨st, hst⟩))) := by congr;
    have hpull:  PrimordialFunctor.map A (Subtype.val) (Sum.inr ⟨st, hst⟩) = @Sum.inr A (_) (⟨(λ p => Set.image Subtype.val (st p)),tempName st hst⟩) := by congr;
    constructor
    rintro y hy
    dsimp only [option]at hy
    simp only [PrimordialFunctor.map_def, Set.mem_iUnion] at hy
    obtain ⟨a,b⟩ := hy
    have := moves_comp _ hcomp a
    rw [hpull] at b
    dsimp [moves,moves_or] at b
    simp only [QPF.Fix.dest_mk] at b
    obtain ⟨w,⟨_,c⟩⟩ := b
    rw [← c]
    exact w.property
    
    
/-
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
  fun hx => Subposition.irrefl x.1 (.of_mem_moves x.2 (by 
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

theorem WSubposition.of_mem_moves {A : Type} {x y : Primordial A} {hy : y ∈ Comp A} (h : x ∈ ⋃ p, (moves.{u} ⟨y, hy⟩) p) :
    WSubposition x y := by
    right
    exact (Subposition.of_mem_moves hy h)

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

#check casesSC




/-- Want to define a new definition that straight up uses recursion -/
noncomputable def MAP' (f : A → B) (x : Primordial.{u} A) : Primordial B := 
--  match val: moves_or x with
  if hx : IsAtom.{u} x then
    mk_atom (f (Sum.getLeft (moves_or x) hx))
  else 
    have h: IsComp x := Sum.not_isLeft.mp hx 
    have hl : ∀ L∈ ⟨x,h⟩ᴸ, Subposition L x := by
      intro L hl
      unfold Subposition
      rw [Relation.transGen_iff]
      rw [option_iff_lroption]
      left
      left
      dsimp [LOption]
      use h
    have hr : ∀ R∈ ⟨x,h⟩ᴿ, Subposition R x := by
      intro R hr
      unfold Subposition
      rw [Relation.transGen_iff]
      rw [option_iff_lroption]
      left
      right
      dsimp [LOption]
      use h
    have lsmall : Small.{u} (Set.range fun z : ⟨x, h⟩ᴸ ↦ MAP' f z) := by
      infer_instance
    have rsmall : Small.{u} (Set.range fun z : ⟨x, h⟩ᴿ ↦ MAP' f z) := by 
      infer_instance
    !{ Set.range (fun z : ⟨x, h⟩ᴸ ↦ MAP' f z)|Set.range (fun z : ⟨x, h⟩ᴿ ↦ MAP' f z)}
termination_by x
decreasing_by Primordial_wf

@[simp] lemma MAP'_atom {A B} {f : A → B} (x : Primordial A) (hx : IsAtom x) :
  MAP' f x = mk_atom (f (Sum.getLeft (moves_or x) hx)) := by
  unfold MAP'
  simp [hx]



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

theorem MAP_comp (f : A → B) (g : B → C) (x : Primordial.{u} A) : MAP' g (MAP' f x) = MAP' (g∘f) x := by
  match h: IsAtom x with
    |true =>
      have h1 : IsAtom (MAP' f x) := sorry
      have h2 : IsAtom (MAP' (g∘ f) x) := sorry
      rw [MAP'_atom _ h1]
      simp [MAP'_atom _ h]
    |false =>
      unfold MAP'
      have h1 : ¬IsAtom (MAP' f x) := sorry
      have h2 : ¬IsAtom (MAP' (g∘f) x) := sorry
      
      sorry
      
noncomputable def sum_AA : Atom A→ Atom B → Atom (A×B) := λ a b => 
let a' :=(Sum.getLeft (@moves_or A a) a.2);
let b' :=(Sum.getLeft (@moves_or B b) b.2);
(mk_atom (a',b'))


noncomputable def sum_AC (g : Atom A) (H : Primordial.{u} B) : Primordial.{u} (A×B) := 
  let g' :A := (Sum.getLeft (@moves_or A g) g.2)
  let f := (λ b:B => (g',b))
  MAP' f H
  

example {A B C : Type} {a : Atom.{u} A} {b : Atom.{u} B} {G : Primordial.{u} C} : 
MAP' (fun ((x1,x2),x3) => (x1,(x2,x3))) (sum_AC (sum_AA a b) G) = sum_AC a (sum_AC b G) := match hg : IsAtom G with 
|true => sorry
|false => sorry



noncomputable def test1 {A} (x : Primordial A) : Nat :=
match IsAtom x with 
| true => 0
| false=> 1
noncomputable def test2 {A} (x : Primordial A) : Prop :=
match IsAtom x with 
| true => True
| false=> ∀ y :Primordial A, option y x -> test2 y
termination_by x
decreasing_by Primordial_wf

noncomputable def test3 {A} (x : Primordial A) : Primordial A :=
if  h : IsAtom x then
   mk_atom (Sum.getLeft (moves_or x) h)
else
 have h' : IsComp x := by
   simp at h
   simp [h]
 mk_comp (Sum.getRight (moves_or x) h')

example {A} (x : Primordial A) : x = test3 x := by
match h: IsAtom x with
|true =>
      dsimp [test3]
      simp [h]
      dsimp [mk_atom]
      dsimp [moves_or]
      simp [QPF.Fix.mk_dest]
|false =>
      dsimp [test3]
      simp [h]
      dsimp [mk_comp]
      dsimp [moves_or]
      simp [QPF.Fix.mk_dest]


example {A B} (x : Atom A) (y : Atom B) : test1 x.1 = test1 y.1 := by 
dsimp [test1] 
have hx :IsAtom x.1 := x.2
have hy :IsAtom y.1 := y.2
simp [hx,hy]

theorem test10 {A} (x : Primordial A) : test2 x  := by
match hx:IsAtom x with
| true =>
  unfold test2
  simp only [hx]
| false =>
  unfold test2
  simp only [hx]
  intro y hy
  exact test10 y
termination_by x
decreasing_by Primordial_wf


end Primordial




-- def D := Unit
-- def z:Unit := Unit.unit





