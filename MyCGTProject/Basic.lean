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

/-- the following lemmas are useful for termination proofs. -/
@[simp]
lemma left_memMoves {A : Type} {x L : Primordial A} : L∈ xᴸ → L∈ ⋃ p, x.moves p := by
  intro hl
  simp only [Set.mem_iUnion, Player.exists]
  left
  exact hl
@[simp]
lemma right_memMoves {A : Type} {x L : Primordial A} : L∈ xᴿ → L∈ ⋃ p, x.moves p := by
  intro hr
  simp only [Set.mem_iUnion, Player.exists]
  right
  exact hr  

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
    -- proof that the game made from a composite form is composite, even when acted on by the map Subtype.val.
    have hcomp : IsComp (QPF.Fix.mk (PrimordialFunctor.map A Subtype.val (Sum.inr ⟨st, hst⟩))) := by congr;
    -- we can pull the "Sum.inr" out of the following thing.
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
    
    

theorem subposition_wf {A : Type} : @WellFounded (Primordial A) Subposition := by
  refine ⟨fun x => Acc.transGen ?x⟩
  exact acc_all x

instance {A : Type} : IsWellFounded (Primordial A) Subposition := ⟨subposition_wf⟩
instance {A : Type} : WellFoundedRelation (Primordial A) := ⟨Subposition, instIsWellFoundedSubposition.wf⟩

theorem Subposition.irrefl {A : Type} (x : Primordial A) : ¬Subposition x x := _root_.irrefl x

theorem option.irrefl {A : Type} (x : Primordial A) : ¬option x x := by
   have h1 := Subposition.irrefl x
   dsimp [Subposition] at h1
   rw [Relation.transGen_iff] at h1
   simp at h1
   exact h1.left


theorem self_notMem_moves (A : Type) (p : Player) (x : Primordial A) : x ∉ moves x p :=  
  fun hx => Subposition.irrefl x (Subposition.of_mem_moves (by 
  simp only [Set.mem_iUnion]
  use p))

/-- `WSubposition x y` is the non-strict version of `Subposition x y`. -/
@[expose]
def WSubposition {A : Type} (x y : Primordial A) : Prop := x = y ∨ Subposition x y

theorem subposition_iff_exists {A : Type} {x y : Primordial A} : Subposition x y ↔
   ∃ p:Player, ∃ z ∈  moves y p, WSubposition x z := by
   unfold WSubposition Subposition
   rw [Relation.transGen_iff]
   dsimp only [option]
   simp_rw [Set.mem_iUnion]   
   constructor
   · intro hmp
     cases hmp with
     | inl hl => 
       let ⟨i,hi⟩ := hl
       use i,x
       constructor
       · exact hi
       · simp only [true_or]
     | inr hr => 
       have ⟨a,⟨bl,⟨i,hi⟩⟩⟩ := hr
       use i,a
       constructor
       · exact hi
       · simp only [bl, or_true]
   · intro hmpr
     obtain ⟨i,c,⟨d1,d2⟩⟩ := hmpr
     cases d2 with 
     | inl hl => 
       left
       use  i
       rw [←hl] at d1
       exact d1
     | inr hr => 
       right
       use c
       constructor
       · exact hr
       · use i


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

theorem subposition_of_wsubposition_of_ne {A : Type} {x y : Primordial A} (hw : WSubposition x y) (hne : x ≠ y) : Subposition x y := hw.resolve_left hne


theorem subposition_of_wsubposition_not_wsubposition {A : Type} {x y : Primordial A}
    (hxy : WSubposition x y) (hyx : ¬WSubposition y x) : Subposition x y :=
  hxy.resolve_left fun h => hyx (wsubposition_of_eq h.symm)

theorem subposition_iff_wsubposition_not_wsubposition {A : Type} {x y : Primordial A} :
    Subposition x y ↔ WSubposition x y ∧ ¬WSubposition y x :=
  ⟨fun hxy => ⟨hxy.wsubposition, hxy.not_wsubposition⟩,
    fun h => subposition_of_wsubposition_not_wsubposition h.1 h.2⟩

theorem WSubposition.of_mem_moves {A : Type} {x y : Primordial A} (h : x ∈ ⋃ p, (moves.{u} y) p) :
    WSubposition x y := by
    right
    exact (Subposition.of_mem_moves h)

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
    [Prod.Lex.left, Prod.Lex.right, PSigma.Lex.left, PSigma.Lex.right, left_memMoves, right_memMoves,
    Subposition.of_mem_moves, Subposition.trans, Subtype.prop] )




/-- Want to define a new definition that straight up uses recursion -/
noncomputable def MAP' (f : A → B) (x : Primordial.{u} A) : Primordial B := 
--  match val: moves_or x with
  if hx : IsAtom.{u} x then
    mk_atom (f (Sum.getLeft (moves_or x) hx))
  else 
    have lsmall : Small.{u} (Set.range fun z : xᴸ ↦ MAP' f z) := by
      infer_instance
    have rsmall : Small.{u} (Set.range fun z : xᴿ ↦ MAP' f z) := by 
      infer_instance
    !{ Set.range (fun (z : xᴸ) ↦ MAP' f z)|Set.range (fun (z : xᴿ) ↦ MAP' f z)}
--    have lsmall : Small.{u} (Set.image (fun z : Primordial A ↦ MAP' f z) (xᴸ))  := by
--      infer_instance
--    have rsmall : Small.{u} (Set.image (fun z : Primordial A ↦ MAP' f z) (xᴿ)) := by 
--      infer_instance
--    have lsmall : Small.{u,u+1} ({w:Primordial B | ∃ z∈ xᴸ, w=MAP' f z})  := by
--      have this: Small.{u,u+1} (Set.range fun z : xᴸ ↦ MAP' f z) := by infer_instance
--      have that : (Set.range fun z : xᴸ ↦ MAP' f z) ≃ {w:Primordial B | ∃ z∈ xᴸ, w=MAP' f z} := sorry
--      apply ((small_congr that).mp this)-
--    have rsmall : Small.{u} ({w:Primordial B | ∃ z: xᴿ, w=MAP' f z}) := sorry


--    !{ (Set.image (fun z : Primordial A ↦ MAP' f z) (xᴸ))|(Set.image (fun z : Primordial A ↦ MAP' f z) (xᴿ))}
-- {w:Primordial B | z∈ xᴸ ∧ w=MAP' f z}

--    !{ {w:Primordial B | ∃ z: xᴸ, w=MAP' f z}|{w:Primordial B | ∃ z: xᴿ, w=MAP' f z}}
termination_by x
decreasing_by Primordial_wf

@[simp] lemma MAP'_mk_atom {A B} {f : A → B} (x : Primordial A) (hx : IsAtom x) :
  MAP' f x = mk_atom (f (Sum.getLeft (moves_or x) hx)) := by
  unfold MAP'
  simp [hx]



@[simp]
lemma MAP'_IsAtom {A B} {f : A → B} {x : Primordial A} :  IsAtom (MAP' f x) =IsAtom x := by
      match h : IsAtom x with
      | true => 
             unfold MAP'
             simp [h, IsAtom]
             
      | false => 
              unfold MAP'
              simp only [h, Bool.false_eq_true, ↓reduceDIte, Sum.isLeft_eq_false]
              dsimp only [ofSets]
              simp only [moves_or_mk_comp_id, Sum.isRight_inr]

lemma image_member {A B : Type} {f : A → B} {x : Primordial.{u} A} {p : Player} :∀ a:Primordial B, (a∈ (MAP' f x).moves p ↔ ∃ w ∈ x.moves p, MAP' f w = a) := 
  by
  intro a
  match h: IsAtom x with
  |true => 
    have h1 : IsAtom (MAP' f x) := by
        simp only [MAP'_IsAtom]
        exact h
    unfold MAP'
    simp only [h,↓reduceDIte]
    have this: IsAtom.{u} (mk_atom (f ((moves_or x).getLeft h))).1 := by congr
    have this' :=isEmpty_iff.mp (Atom_no_options _ this)
    have this'':= isEmpty_iff.mp (Atom_no_options _ h)
    constructor
    · intro h'
      exfalso
      contradiction
    · intro ⟨w,⟨_,_⟩⟩
      have this': w.option x := by 
        dsimp [option]
        simp only [Set.mem_iUnion]
        use p
      exfalso
      exact this'' ⟨w,this'⟩
  |false => 
    have h1 : ¬IsAtom (MAP' f x) := by
        simp only [MAP'_IsAtom,h, Bool.false_eq_true, not_false_eq_true]
    constructor
    · intro h'
      unfold MAP' at h'
      simp only [h,Bool.false_eq_true, ↓reduceDIte, moves_ofSets, Player.cases] at h'
      cases p <;> (simp only [Set.mem_range, Subtype.exists, exists_prop] at h' ; exact h')
    · intro ⟨w,⟨_,_⟩⟩
      unfold MAP'
      simp only [h,Bool.false_eq_true, ↓reduceDIte]
      cases p <;> (simp only [moves_ofSets, Player.cases, Set.mem_range, Subtype.exists, exists_prop]; use w)

theorem MAP_comp {A B C : Type} (f : A → B) (g : B → C) (x : Primordial.{u} A) : MAP' g (MAP' f x) = MAP' (g∘f) x := by
  match h: IsAtom x with
    |true =>
      have h1 : IsAtom (MAP' f x) := by 
        simp only [MAP'_IsAtom,h]
      rw [MAP'_mk_atom _ h1]
      simp [MAP'_mk_atom _ h]
    |false =>
       have h1 : ¬IsAtom (MAP' f x) := by
        simp only [MAP'_IsAtom,h, Bool.false_eq_true, not_false_eq_true]
       -- after unfolding the definition of MAP', this is the only thing that remains to be shown. 
       --It relies recursively on MAP_comp, 
       --so (regrettably) we cannot extract the proof of this to a lemma.
       have hrange :∀ p:Player, Set.range (fun z: moves (MAP' f x) p => MAP' g z) = Set.range (fun z: moves x p => MAP' (g∘f) z) :=by 
        intro p
        ext t
        -- We prove that two sets are equal by proving that, a is in one iff a is in the other.
        constructor 
        ·    intro h'
             obtain ⟨a,b⟩ := h'
             have this : ∃ w: moves x p, MAP' f w = a := by simp only [Subtype.exists, exists_prop, (image_member a.1).mp (a.property)]
             simp only at b
             dsimp [Set.range]
             obtain ⟨w1,w2⟩ := this
             have : ↑w1 ∈ ⋃ p, (moves x) p := by
                  simp only [Set.mem_iUnion]
                  use p
                  exact w1.property
             use w1
             rw [← MAP_comp, w2,b]
        ·    intro h'
             obtain ⟨a,b⟩ := h'
             have : a.1∈ x.moves p := by exact a.property;
             have : ↑a ∈ ⋃ p, (moves x) p := Set.mem_iUnion.mpr (by use p);
             have : (MAP' f a)∈ (MAP' f x).moves p := 
                  (image_member (MAP' f a)).mpr (by use a);
             simp only at b
             rw [← MAP_comp] at b
             dsimp [Set.range]
             simp only [Subtype.exists, exists_prop]
             use (MAP' f a)
       unfold MAP';simp only [h1,h, Bool.false_eq_true, ↓reduceDIte];
       simp only [hrange]
termination_by x
decreasing_by Primordial_wf

-- noncomputable def sum_AA : Atom A→ Atom B → Atom (A×B) := λ a b => 
-- let a' :=(Sum.getLeft (@moves_or A a) a.2);
-- let b' :=(Sum.getLeft (@moves_or B b) b.2);
-- (mk_atom (a',b'))


-- noncomputable def sum_AC (g : Atom A) (H : Primordial.{u} B) : Primordial.{u} (A×B) := 
--   MAP' (λ b:B => ((Sum.getLeft (@moves_or A g) g.2),b)) H

noncomputable def old_sum {A B : Type} (x : Primordial A) (y : Primordial B) : Primordial (A×B) :=
if hx : IsAtom x then
  if hy : IsAtom y then 
    mk_atom (Sum.getLeft (moves_or x) hx,Sum.getLeft (moves_or y) hy)
  else 
    MAP' (λ b:B => ((Sum.getLeft (moves_or x) hx),b)) y
else
  if hy:IsAtom y then 
    MAP' (λ a:A => (a,(Sum.getLeft (moves_or y) hy))) x
  else 
    !{ (Set.range fun z : xᴸ ↦ old_sum z.val y)∪(Set.range fun z : yᴸ ↦ old_sum x z.val)|(Set.range fun z : xᴿ ↦ old_sum z.val y)∪(Set.range fun z : yᴿ ↦ old_sum x z.val)}
termination_by (x,y)
decreasing_by Primordial_wf

noncomputable def sum {A B : Type} (x : Primordial A) (y : Primordial B) : Primordial (A×B) :=
if hxy:IsAtom x ∧IsAtom y then mk_atom (Sum.getLeft (moves_or x) hxy.left,Sum.getLeft (moves_or y) hxy.right)
else !{ (Set.range fun z : xᴸ ↦ sum z.val y)∪(Set.range fun z : yᴸ ↦ sum x z.val)|(Set.range fun z : xᴿ ↦ sum z.val y)∪(Set.range fun z : yᴿ ↦ sum x z.val)}
termination_by (x,y)
decreasing_by Primordial_wf

/-- pairwise subposition relation useful in proving things via joint induction (ideally) -/
def pairSubposition {A B : Type} := Prod.GameAdd (@Subposition A) (@Subposition B)

lemma old_sum_to_MAP'_fst {A B : Type} (x : Primordial A) (y : Primordial B) (hy : IsAtom y) : old_sum x y =  MAP' (λ a:A => (a,(Sum.getLeft (moves_or y) hy))) x := by
match hx:IsAtom x with
|true=> 
  unfold old_sum MAP'
  simp only [hx, hy,↓reduceDIte]  
|false =>
  unfold old_sum MAP'
  simp [hx, hy,Bool.false_eq_true, ↓reduceDIte]
  

lemma old_sum_eq_sum_fst {A B : Type} (x : Primordial A) (y : Primordial B) (hy : IsAtom y) : old_sum x y = sum x y := by
match hx:IsAtom x with
|true =>   
  unfold old_sum sum
  simp only [hx,  hy, and_self,↓reduceDIte]
|false =>
  unfold old_sum sum MAP'
  simp only [hx, hy,Bool.false_eq_true, and_true,↓reduceDIte]  
  congr
  · ext t
    simp only [Set.mem_range, Subtype.exists, exists_prop, Set.mem_union]
    constructor
    · intro ⟨z,⟨ha1,ha2⟩⟩
      left
      use z
      rw [←old_sum_eq_sum_fst _ _ hy]
      constructor
      · exact ha1
      · rw [old_sum_to_MAP'_fst _ _ hy]
        exact ha2
    · intro h
      match h with
      |Or.inl h' =>
        obtain ⟨a,⟨ha1,ha2⟩⟩:= h'
        use a
        constructor
        · exact ha1
        · rw [← old_sum_to_MAP'_fst _ _ hy]
          rw [old_sum_eq_sum_fst _ _ hy]
          exact ha2
      |Or.inr h'=> 
        obtain ⟨b,⟨hb1,hb2⟩⟩ := h'
        exfalso
        exact isEmpty_iff.mp (Atom_no_options _ hy) ⟨b,left_memMoves hb1⟩
  · ext t
    simp only [Set.mem_range, Subtype.exists, exists_prop, Set.mem_union]
    constructor
    · intro ⟨z,⟨ha1,ha2⟩⟩
      left
      use z
      rw [←old_sum_eq_sum_fst _ _ hy]
      constructor
      · exact ha1
      · rw [old_sum_to_MAP'_fst _ _ hy]
        exact ha2
    · intro h
      match h with
      |Or.inl h' =>
        obtain ⟨a,⟨ha1,ha2⟩⟩:= h'
        use a
        constructor
        · exact ha1
        · rw [← old_sum_to_MAP'_fst _ _ hy]
          rw [old_sum_eq_sum_fst _ _ hy]
          exact ha2
      |Or.inr h'=> 
        obtain ⟨b,⟨hb1,hb2⟩⟩ := h'
        exfalso
        exact isEmpty_iff.mp (Atom_no_options _ hy) ⟨b,right_memMoves hb1⟩
termination_by x
decreasing_by Primordial_wf

lemma old_sum_to_MAP'_snd {A B : Type} (x : Primordial A) (hx : IsAtom x) (y : Primordial B) : old_sum x y =  MAP' (λ b:B => ((Sum.getLeft (moves_or x) hx),b)) y := by
match hy : IsAtom y with
|true=> 
  unfold old_sum MAP'
  simp only [hx, hy,↓reduceDIte]  
|false =>
  unfold old_sum MAP'
  simp [hx, hy,Bool.false_eq_true, ↓reduceDIte]
  

lemma old_sum_eq_sum_snd {A B : Type} (x : Primordial A) (hx : IsAtom x) (y : Primordial B) : old_sum x y = sum x y := by
match hy:IsAtom y with
|true =>   
  unfold old_sum sum
  simp only [hx,  hy, and_self,↓reduceDIte]
|false =>
  unfold old_sum sum MAP'
  simp only [hx, hy,Bool.false_eq_true, ↓reduceDIte]  
  congr
  · ext t
    simp only [Set.mem_range, Subtype.exists, exists_prop, Set.mem_union]
    constructor
    · intro ⟨z,⟨ha1,ha2⟩⟩
      right
      use z
      rw [←old_sum_eq_sum_snd _ hx _]
      constructor
      · exact ha1
      · rw [old_sum_to_MAP'_snd _ hx _]
        exact ha2
    · intro h
      match h with
      |Or.inl h'=> 
        obtain ⟨b,⟨hb1,hb2⟩⟩ := h'
        exfalso
        exact isEmpty_iff.mp (Atom_no_options _ hx) ⟨b,left_memMoves hb1⟩
      |Or.inr h' =>
        obtain ⟨a,⟨ha1,ha2⟩⟩:= h'
        use a
        constructor
        · exact ha1
        · rw [← old_sum_to_MAP'_snd _ hx _]
          rw [old_sum_eq_sum_snd _ hx _]
          exact ha2
  · ext t
    simp only [Set.mem_range, Subtype.exists, exists_prop, Set.mem_union]
    constructor
    · intro ⟨z,⟨ha1,ha2⟩⟩
      right
      use z
      rw [←old_sum_eq_sum_snd _ hx _]
      constructor
      · exact ha1
      · rw [old_sum_to_MAP'_snd _ hx _]
        exact ha2
    · intro h
      match h with
      |Or.inl h'=> 
        obtain ⟨b,⟨hb1,hb2⟩⟩ := h'
        exfalso
        exact isEmpty_iff.mp (Atom_no_options _ hx) ⟨b,right_memMoves hb1⟩
      |Or.inr h' =>
        obtain ⟨a,⟨ha1,ha2⟩⟩:= h'
        use a
        constructor
        · exact ha1
        · rw [← old_sum_to_MAP'_snd _ hx _]
          rw [old_sum_eq_sum_snd _ hx _]
          exact ha2
termination_by y
decreasing_by Primordial_wf


theorem old_sum_eq_sum {A B : Type} (x : Primordial A) (y : Primordial B) : old_sum x y = sum x y := by
match hx:IsAtom x, hy:IsAtom y with
|true,true => 
  unfold old_sum sum
  simp only [hx,  hy, and_self,↓reduceDIte]
--
|true,false =>
  exact old_sum_eq_sum_snd _ hx _
--
|false,true =>  
   exact old_sum_eq_sum_fst _ _ hy
--
|false,false => 
  unfold old_sum sum MAP'
  simp only [hx, hy,Bool.false_eq_true, and_self,↓reduceDIte]
  congr
  · ext t
    rw [old_sum_eq_sum]
  · ext t
    rw [old_sum_eq_sum]
  · ext t
    rw [old_sum_eq_sum]
  · ext t
    rw [old_sum_eq_sum]
termination_by (x,y)
decreasing_by Primordial_wf





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




-- example {A B C : Type} {a : Atom.{u} A} {b : Atom.{u} B} {G : Primordial.{u} C} : 
-- MAP' (fun ((x1,x2),x3) => (x1,(x2,x3))) (sum_AC (sum_AA a b) G) = sum_AC a (sum_AC b G) := by
--   match hg : IsAtom G with 
-- |true => 
--       simp
--       have t1: IsAtom (sum_AA a b).1 := sorry
--       have h' : (fun x => sum_AC (sum_AA a b) x) G = (sum_AC (sum_AA a b) G):= by simp only; rfl;
--       have t2: IsAtom (sum_AC (sum_AA a b) G) := by
--         rw [←h']
--         have temp := @MAP'_IsAtom _ ((A×B)×C) (fun x : C => ((Sum.getLeft (moves_or a.1) a.2,Sum.getLeft (moves_or b.1) b.2),x)) G 
--         sorry
--       unfold MAP'
--       split_ifs with h
--       ·     
--         unfold sum_AC
--         simp only [hg, MAP'_mk_atom, moves_or_mk_atom_id, Sum.getLeft_inl]
--         unfold MAP'
--         simp
--         _
--       ·contradiction
        
-- |false => sorry



-- noncomputable def test1 {A} (x : Primordial A) : Nat :=
-- match IsAtom x with 
-- | true => 0
-- | false=> 1
-- noncomputable def test2 {A} (x : Primordial A) : Prop :=
-- match IsAtom x with 
-- | true => True
-- | false=> ∀ y :Primordial A, option y x -> test2 y
-- termination_by x
-- decreasing_by Primordial_wf

-- noncomputable def test3 {A} (x : Primordial A) : Primordial A :=
-- if  h : IsAtom x then
--    mk_atom (Sum.getLeft (moves_or x) h)
-- else
--  have h' : IsComp x := by
--    simp at h
--    simp [h]
--  mk_comp (Sum.getRight (moves_or x) h')

-- example {A} (x : Primordial A) : x = test3 x := by
-- match h: IsAtom x with
-- |true =>
--       dsimp [test3]
--       simp [h]
--       dsimp [mk_atom]
--       dsimp [moves_or]
--       simp [QPF.Fix.mk_dest]
-- |false =>
--       dsimp [test3]
--       simp [h]
--       dsimp [mk_comp]
--       dsimp [moves_or]
--       simp [QPF.Fix.mk_dest]


-- example {A B} (x : Atom A) (y : Atom B) : test1 x.1 = test1 y.1 := by 
-- dsimp [test1] 
-- have hx :IsAtom x.1 := x.2
-- have hy :IsAtom y.1 := y.2
-- simp [hx,hy]

-- theorem test10 {A} (x : Primordial A) : test2 x  := by
-- match hx:IsAtom x with
-- | true =>
--   unfold test2
--   simp only [hx]
-- | false =>
--   unfold test2
--   simp only [hx]
--   intro y hy
--   exact test10 y
-- termination_by x
-- decreasing_by Primordial_wf


end Primordial




-- def D := Unit
-- def z:Unit := Unit.unit





