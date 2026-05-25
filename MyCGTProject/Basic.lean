-- This code is based on code by Violeta Hernández Palacios. Her work can be found here: https://github.com/vihdzp/combinatorial-games
import Mathlib.Logic.Small.Set
import Mathlib.Data.Set.Image
import Mathlib.Data.Set.Basic
import MyCGTProject.SmallNonempty
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
  fun x => @QPF.Fix.dest (PrimordialFunctor A) (QPF_PrimordialFunctor A) x


noncomputable abbrev IsAtom {A : Type} (x : Primordial A):= Sum.isLeft (moves_or x)
noncomputable abbrev IsComp {A : Type} (x : Primordial A) := Sum.isRight (moves_or x)


noncomputable def Atom (A : Type) := {x: Primordial A | IsAtom x}
noncomputable def Comp (A : Type) := {x : Primordial A | IsComp x}


noncomputable def mk_atom {A : Type} : A → Primordial A := fun a => 
(@QPF.Fix.mk (PrimordialFunctor A) (QPF_PrimordialFunctor A) (@Sum.inl A {st : Player → Set (Primordial A) // ∀ p, Small (st p)} a))
noncomputable def mk_comp {A : Type} (s : {st : Player → Set (Primordial A) // ∀ p, Small (st p)}) : Primordial A := (@QPF.Fix.mk (PrimordialFunctor A) (QPF_PrimordialFunctor A) (@Sum.inr A {st : Player → Set (Primordial A) // ∀ p, Small (st p)} s))


lemma mk_atom_IsAtom {A : Type} {x : A} : IsAtom (mk_atom x) := by congr
lemma mk_comp_IsComp {A : Type} {x : {st : Player → Set (Primordial A) // ∀ p, Small (st p)}} : IsComp (mk_comp x) := by congr


@[simp]
theorem mk_moves_or_id {A : Type} (x : Primordial A) : QPF.Fix.mk (moves_or x) = x:= by 
  dsimp [moves_or]
  rw [QPF.Fix.mk_dest]


@[simp]
theorem mk_atom_moves_or_id {A : Type} (x : Atom A) : mk_atom (Sum.getLeft (moves_or x.1) x.2) = x := by 
  unfold mk_atom
  rw [Sum.inl_getLeft, mk_moves_or_id]
@[simp]
theorem mk_comp_moves_or_id {A : Type} (x : Comp A) : mk_comp (Sum.getRight (moves_or x.1) x.2) = x := by 
  unfold mk_comp
  rw [Sum.inr_getRight, mk_moves_or_id]


@[simp]
theorem moves_or_mk_comp_id {A : Type} (st : Player → Set (Primordial A)) (h : ∀ p, Small (st p)) : moves_or (mk_comp ⟨st, h⟩) = Sum.inr ⟨st, h⟩ := by 
        dsimp [moves_or,mk_comp]
        rw [QPF.Fix.dest_mk] 
@[simp]
theorem moves_or_mk_atom_id {A : Type} (x : A) : moves_or (mk_atom x) = Sum.inl x := by 
        dsimp [moves_or,mk_atom]
        rw [QPF.Fix.dest_mk] 



-- Special Games
theorem Atom_nComp_iff {A : Type} {x : Primordial A} : IsAtom x=true ↔ ¬(IsComp x=true) := by
  simp only [Bool.not_eq_true, Sum.isRight_eq_false]
theorem Comp_nAtom_iff {A : Type} {x : Primordial A} : IsComp x=true ↔ ¬(IsAtom x=true) := by
  simp only [Bool.not_eq_true,Sum.isLeft_eq_false]


namespace Primordial
export Player (left right)
-----------------------------------------------------------------------------------

/-! ### OfSetsPrimordial -/


/--
definition  of the `ofSets` operation.
Used to implement the `!{st}` and `!{s | t}` syntax.
Here we construct a combinatorial Set Coloring game from its left and right sets. -/
@[no_expose]
noncomputable instance ofSetsSC {A : Type} : OfSets (Primordial A) (fun _ => True)
where ofSets st _ _ _ := @mk_comp A ⟨st , by intro p; cases p <;> assumption⟩



lemma ofSets_IsComp {A : Type} (st : Player → Set (Primordial A)) [Small.{u} (st left)] [Small.{u} (st right)] : IsComp (!{st}) := by
  dsimp [IsComp, ofSets]
  rw [moves_or_mk_comp_id]
  rw [Sum.isRight_inr]


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
   moves !{st} p= st p:= by 
  dsimp [ofSets, moves]
  ext x
  dsimp [moves]
  simp only [moves_or_mk_comp_id]
  rw [dif_pos (by dsimp [IsComp];rw [moves_or_mk_comp_id,Sum.isRight_inr]), Sum.getRight_inr]

@[simp]
theorem ofSets_moves {A : Type} (x : Primordial A) (h : IsComp x) : !{(moves x)}  = x  := by
  dsimp [ ofSets]
  unfold moves
  simp [h]
  dsimp [mk_comp,moves_or]
  simp [QPF.Fix.mk_dest]

--@[game_cmp]
theorem leftMoves_ofSets (s t : Set (Primordial A)) [Small.{u} s] [Small.{u} t] : !{s|t}ᴸ = s := moves_ofSets (Player.cases s t) left

--@[game_cmp]
theorem rightMoves_ofSets (s t : Set (Primordial A)) [Small.{u} s] [Small.{u} t] : !{s|t}ᴿ = t := moves_ofSets (Player.cases s t) right

@[simp]
theorem ofSets_leftMoves_rightMoves (x : Primordial A) (h : IsComp x) : !{xᴸ | xᴿ} = x :=  by 
  convert (ofSets_moves x h) with p
  funext p
  cases p <;> dsimp [Player.cases]

@[ext]
theorem ext {A : Type} (x y : Comp A) (hxy : ∀ p, moves x.val p = moves y.val p) : x = y :=  by
    have hx : IsComp x.1 := by use x.2 
    have hy : IsComp y.1 := by use y.2
    have thisx : x= ⟨x.1,hx⟩ := by simp
    have thisy : y= ⟨y.1,hy⟩ := by simp
    ext
    rw [← ofSets_moves x.1 hx  , ← ofSets_moves y.1 hy ]
    simp_rw [funext hxy]


theorem ofSets_inj' {A : Type} {st₁ st₂ : Player → Set (Primordial.{u} A)}
    [Small (st₁ left)] [Small (st₁ right)] [Small (st₂ left)] [Small (st₂ right)] :
    !{st₁} =!{st₂}↔ st₁ = st₂ := by
    have h1 := ofSets_IsComp st₁
    have h2 := ofSets_IsComp st₂
    let this1 : Comp A := ⟨!{st₁},h1⟩
    let this2 : Comp A := ⟨!{st₂},h2⟩
    have :this1 = this2 ↔ !{st₁} =!{st₂} := by 
      dsimp [this1,this2]
      simp
    rw [← this]
    simp_rw [Primordial.ext_iff]
    constructor
    · intro h
      funext p
      rw [ ← moves_ofSets st₁ p]
      rw [ ← moves_ofSets st₂ p]
      exact h p
    · intro h
      apply funext_iff.mp at h
      intro p
      rw [  moves_ofSets st₁ p]
      rw [  moves_ofSets st₂ p]
      exact h p


--    simp_rw [← moves_ofSets, funext_iff]
    

theorem ofSets_inj {A : Type} {s₁ s₂ t₁ t₂ : Set (Primordial A)} [Small s₁] [Small s₂] [Small t₁] [Small t₂] :
    !{s₁ | t₁} = !{s₂ | t₂} ↔ s₁ = s₂ ∧ t₁ = t₂ := by
      have this: Player.cases s₁ t₁ =Player.cases s₂ t₂ ↔ s₁ = s₂ ∧ t₁ =t₂ := by
        simp
      have this2 : !{(Player.cases s₁ t₁)} = !{(Player.cases s₂ t₂)}  ↔ Player.cases s₁ t₁  = Player.cases s₂ t₂ := by
        constructor
        · intro h
          funext p
          rw [ ← moves_ofSets (Player.cases s₁ t₁) p]
          rw [ ← moves_ofSets (Player.cases s₂ t₂) p]
          rw [h]          
        · intro h
          simp [h]
      simp [this2,this]
        
-- Because of the diffference between composite and atomic games, we must define subpositions very carefully.

/-- option x y : y is composite and x is in the left or right set of the game y. -/
abbrev option {A : Type} : (Primordial.{u} A) → (Primordial.{u} A) → Prop := fun x y =>  x ∈ ⋃ p, (moves.{u} y) p

/-- x is a left option of the game y -/
abbrev LOption {A : Type} : (Primordial.{u} A) → (Primordial.{u} A) → Prop := fun x y => x ∈ (moves.{u} y) left

/-- x is a right option of the game y -/
abbrev ROption {A : Type} : (Primordial.{u} A) → (Primordial.{u} A) → Prop := fun x y => x ∈ (moves.{u} y) right


/-- x is an option of y iff x is a left or right option of y. -/
theorem option_iff_lroption {x y : Primordial A} : option x y ↔ LOption x y ∨ ROption x y := by 
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

@[simp] lemma leftORright_memMoves {A : Type} {x x' : Primordial A} : x'∈ xᴸ ∨ x'∈ xᴿ ↔ x'∈ ⋃ p, x.moves p := by
  simp

lemma option_IsComp {A : Type} {x y : Primordial A} : x.option y → IsComp y := by
  intro h
  dsimp [option,moves] at h
  simp only [Set.mem_iUnion, Player.exists] at h
  match h':IsComp y with
  | true => rfl
  | false =>
    exfalso
    simp only [h', Bool.false_eq_true, ↓reduceDIte, Set.mem_empty_iff_false, or_self] at h

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

lemma Subposition.of_mem_movesP {A : Type} {x y : Primordial A} {p : Player} (h : x ∈ (moves.{u} y) p) : Subposition x y := by
  suffices x∈ ⋃ p, (moves.{u} y) p by exact Subposition.of_mem_moves this
  · rw [Set.mem_iUnion]
    use p  

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
    exact small_of_injective (h3);
  · have h1 := Atom_no_options x h;
    simp only [@small_isEmpty {y : Primordial A // y.option x} h1]
    

instance small_setOf_subposition {A : Type} (x : Primordial.{u} A) : Small.{u} {y : Primordial A  | Subposition y x} :=
  small_transGen' _ x 

-- -------------------------------------------------  

lemma tempName {α : Type (u + 1)} {q : α → Prop}
(st : Player → Set (Subtype q))
(hst : st ∈ {s: Player → Set (Subtype q)|∀ p, Small.{u} (s p)}) : (λ p => Set.image Subtype.val (st p)) ∈ {s: Player→Set α| ∀ p, Small.{u} (s p)} := by 
  simp only [Player.forall, Set.mem_setOf_eq] at hst ⊢
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
   rw [or_iff_not_and_not] at h1
   apply of_not_not at h1
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
  `(tactic| all_goals { solve_by_elim $config
    [Prod.Lex.left, Prod.Lex.right, PSigma.Lex.left, PSigma.Lex.right, left_memMoves, right_memMoves, Subposition.of_mem_movesP,
    Subposition.of_mem_moves, Subposition.trans, Subtype.prop]} )




/-- returns the dual of a game. If a game is atomic, does nothing. -/
noncomputable def Dual {A : Type} (x : Primordial A) : Primordial A :=
if IsAtom x then 
  x
else
  !{fun p=>Set.range (fun (z : x.moves (-p)) ↦ Dual z)}
termination_by x
decreasing_by 
  Primordial_wf

lemma Dual_IsAtom {A : Type} {x : Primordial A} : IsAtom (Dual x) = IsAtom x:= by
  unfold Dual
  cases h:IsAtom x
  case true =>
       rw [if_pos rfl]
       exact h
  case false =>
       rw [if_neg (by simp)]
       dsimp [ofSets, IsAtom]
       rw [moves_or_mk_comp_id]
       rw [Sum.isLeft_inr]

theorem Dual_selfInverse {A : Type} {x : Primordial A} : Dual ( Dual x) = x := by
  unfold Dual 
  cases h:IsAtom x 
  case true =>
       have: IsAtom x.Dual = true := by rw [Dual_IsAtom]; exact h
       rw [if_pos this]
       unfold Dual
       rw [if_pos h]
  case false =>
       have: IsAtom x.Dual = false := by rw [Dual_IsAtom]; exact h
       rw [if_neg (by simp [this])]
       rw [← ofSets_moves x (by simp [h,Comp_nAtom_iff])]
       congr
       funext p
       ext t
       constructor
       · intro ⟨⟨t',ht1⟩,ht2⟩
         simp only at ht2 
         rw [ofSets_moves _ (by simp [h, Comp_nAtom_iff])] at ht1
         conv at ht1 =>
           unfold Dual
         rw [if_neg (by simp [h])] at ht1
         rw [← ht2]
         rw [moves_ofSets] at ht1
         rw [Set.mem_range] at ht1
         rw [Subtype.exists, neg_neg] at ht1 
         obtain ⟨a,hoa,ha⟩ := ht1
         rw [← ha]
         rw [Dual_selfInverse]
         congr
       · intro ht
         rw [Set.mem_range]
         rw [Subtype.exists] 
         rw [ofSets_moves _ (by simp [h, Comp_nAtom_iff])]
         use Dual t
         have : t.Dual ∈ x.Dual.moves (-p) := by 
              conv =>
                left
                unfold Dual
                rw [if_neg (by simp [h])]
                rw [moves_ofSets]
              rw [Set.mem_range, Subtype.exists, neg_neg]
              use t,ht
         use this
         simp only
         exact Dual_selfInverse
termination_by x
decreasing_by Primordial_wf

theorem Dual_ofSets {A : Type} {L R : Set (Primordial A)} [Small L] [Small R] : Dual !{L|R } =   !{Set.range (fun (z : R) ↦ Dual z) | Set.range (fun (z : L) ↦ Dual z)} :=by
  rw [Dual]
  have := Comp_nAtom_iff.mp <| ofSets_IsComp <| Player.cases L R
  rw [if_neg this]
  congr
  ext p _
  cases p <;> simp

theorem Dual_option {A : Type} {g g' : Primordial A} {p : Player} (hg' : g' ∈ moves g p) : Dual g' ∈ moves (Dual g) (-p) := by 
  have hag :¬ IsAtom g = true := by 
       grind [= eq_def, = moves.eq_def, = IsAtom.eq_def]
  unfold Dual
  conv => 
    left
    unfold Dual
  rw [if_neg hag]
  cases h:IsAtom g'
  · rw [if_neg (by simp)]
    cases p
    · rw [Player.neg_left,moves_ofSets, Player.neg_right, Set.mem_range, Subtype.exists]
      use g', hg'
      simp [h]
    · rw [Player.neg_right, moves_ofSets, Player.neg_left, Set.mem_range, Subtype.exists]
      use g', hg'
      simp [h]
  · rw [if_pos (by simp), moves_ofSets, Set.mem_range, Subtype.exists, neg_neg]
    use g', hg'
    simp [h]

/-- given a function on the underlying sets A, B, this is the function from Primordial A to Primordial B that naturally arises. uses recursion -/
noncomputable def MAP (f : A → B) (x : Primordial.{u} A) : Primordial B := 
--  match val: moves_or x with
  if hx : IsAtom.{u} x then
    mk_atom (f (Sum.getLeft (moves_or x) hx))
  else 
    !{(fun p:Player => Set.range (fun (z: moves x p) => MAP f z))}
termination_by x
decreasing_by 
  Primordial_wf

@[simp] lemma MAP_mk_atom {A B} {f : A → B} (x : Primordial A) (hx : IsAtom x) :
  MAP f x = mk_atom (f (Sum.getLeft (moves_or x) hx)) := by
  unfold MAP
  simp [hx]



@[simp]
lemma MAP_IsAtom {A B} {f : A → B} {x : Primordial A} :  IsAtom (MAP f x) =IsAtom x := by
      match h : IsAtom x with
      | true => 
             unfold MAP
             simp [h, IsAtom]
             
      | false => 
              unfold MAP
              simp only [h, Bool.false_eq_true, ↓reduceDIte, Sum.isLeft_eq_false]
              dsimp only [ofSets]
              simp only [moves_or_mk_comp_id, Sum.isRight_inr]

lemma image_member {A B : Type} {f : A → B} {x : Primordial.{u} A} {p : Player} :∀ a:Primordial B, (a∈ (MAP f x).moves p ↔ ∃ w ∈ x.moves p, MAP f w = a) := 
  by
  intro a
  match h: IsAtom x with
  |true => 
    have h1 : IsAtom (MAP f x) := by
        simp only [MAP_IsAtom]
        exact h
    unfold MAP
    simp only [h,↓reduceDIte]
    have this:= @mk_atom_IsAtom.{u} _ (f ((moves_or x).getLeft h))
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
    have h1 : ¬IsAtom (MAP f x) := by
        simp only [MAP_IsAtom,h, Bool.false_eq_true, not_false_eq_true]
    constructor
    · intro h'
      unfold MAP at h'
      simp only [h,Bool.false_eq_true, ↓reduceDIte, moves_ofSets] at h'
      cases p <;> (simp only [Set.mem_range, Subtype.exists, exists_prop] at h' ; exact h')
    · intro ⟨w,⟨_,_⟩⟩
      unfold MAP
      simp only [h,Bool.false_eq_true, ↓reduceDIte]
      cases p <;> (simp only [moves_ofSets, Set.mem_range, Subtype.exists, exists_prop]; use w)

theorem MAP_comp {A B C : Type} (f : A → B) (g : B → C) (x : Primordial.{u} A) : MAP g (MAP f x) = MAP (g∘f) x := by
  match h: IsAtom x with
    |true =>
      have h1 : IsAtom (MAP f x) := by 
        simp only [MAP_IsAtom,h]
      rw [MAP_mk_atom _ h1]
      simp [MAP_mk_atom _ h]
    |false =>
       have h1 : ¬IsAtom (MAP f x) := by
        simp only [MAP_IsAtom,h, Bool.false_eq_true, not_false_eq_true]
       -- after unfolding the definition of MAP, this is the only thing that remains to be shown. 
       --It relies recursively on MAP_comp, 
       --so (regrettably) we cannot extract the proof of this to a lemma.
       have hrange :∀ p:Player, Set.range (fun z: moves (MAP f x) p => MAP g z) = Set.range (fun z: moves x p => MAP (g∘f) z) :=by 
        intro p
        ext t
        -- We prove that two sets are equal by proving that, a is in one iff a is in the other.
        constructor 
        ·    intro h'
             obtain ⟨a,b⟩ := h'
             have this : ∃ w: moves x p, MAP f w = a := by simp only [Subtype.exists, exists_prop, (image_member a.1).mp (a.property)]
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
             have : (MAP f a)∈ (MAP f x).moves p := 
                  (image_member (MAP f a)).mpr (by use a);
             simp only at b
             rw [← MAP_comp] at b
             dsimp [Set.range]
             simp only [Subtype.exists, exists_prop]
             use (MAP f a)
       unfold MAP;simp only [h1,h, Bool.false_eq_true, ↓reduceDIte];
       simp only [hrange]
termination_by x
decreasing_by Primordial_wf

-- noncomputable def sum_AA : Atom A→ Atom B → Atom (A×B) := λ a b => 
-- let a' :=(Sum.getLeft (@moves_or A a) a.2);
-- let b' :=(Sum.getLeft (@moves_or B b) b.2);
-- (mk_atom (a',b'))


-- noncomputable def sum_AC (g : Atom A) (H : Primordial.{u} B) : Primordial.{u} (A×B) := 
--   MAP (λ b:B => ((Sum.getLeft (@moves_or A g) g.2),b)) H

private noncomputable def old_sum {A B : Type} (x : Primordial A) (y : Primordial B) : Primordial (A×B) :=
if hx : IsAtom x then
  if hy : IsAtom y then 
    mk_atom (Sum.getLeft (moves_or x) hx,Sum.getLeft (moves_or y) hy)
  else 
    MAP (λ b:B => ((Sum.getLeft (moves_or x) hx),b)) y
else
  if hy:IsAtom y then 
    MAP (λ a:A => (a,(Sum.getLeft (moves_or y) hy))) x
  else 
    !{ (  fun p:Player => (Set.range fun (z : moves x p) ↦ old_sum z.val y)∪(Set.range fun (z : moves y p) ↦ old_sum x z.val)  )}
termination_by (x,y)
decreasing_by 
  cases p <;> Primordial_wf
  cases p
  Primordial_wf
  
noncomputable def sum {A B : Type} (x : Primordial A) (y : Primordial B) : Primordial (A×B) :=
if hxy:IsAtom x ∧IsAtom y then mk_atom (Sum.getLeft (moves_or x) hxy.left,Sum.getLeft (moves_or y) hxy.right)
else !{ (  fun p:Player => (Set.range fun (z : moves x p) ↦ sum z.val y)∪(Set.range fun (z : moves y p) ↦ sum x z.val)  )}
termination_by (x,y)
decreasing_by 
  Primordial_wf

-- 
noncomputable instance {A B : Type} : HAdd (Primordial A) (Primordial B) (Primordial (A×B)) where
  hAdd a b := sum a b


@[simp] lemma sum_format {A B : Type} {a : Primordial A} {b : Primordial B} :  sum a b = a + b := by dsimp [HAdd.hAdd]

/-- The sum of two games is atomic iff both games are atomic. -/
lemma sum_IsAtom {A B : Type} {a : Primordial A} {b : Primordial B} : (IsAtom ( a +b)=true) ↔ IsAtom a ∧ IsAtom b := by
  dsimp [HAdd.hAdd]
  cases ha : IsAtom a
  · unfold sum
    simp only [ha, Bool.false_eq_true, false_and, ↓reduceDIte,]
    dsimp [ofSets]
    simp
  · cases hb : IsAtom b
    · unfold sum
      simp only [ha,hb, Bool.false_eq_true, and_false, ↓reduceDIte,]
      dsimp [ofSets]
      simp
    · unfold sum
      simp [ha,hb]
      dsimp [IsAtom]
      simp

lemma sum_LOption {A B : Type} {x : Primordial (A × B)} {a : Primordial A} {b : Primordial B} : x.LOption (a+b) ↔ (∃ a':Primordial A, a'.LOption a ∧ x= (a'+b)) ∨ (∃ b':Primordial B, b'.LOption b ∧ x= (a+b')) := by
  constructor
  · intro h
    have t := (not_iff_not.mpr <| sum_IsAtom).mp <| Comp_nAtom_iff.mp <| option_IsComp 
         <| option_iff_lroption.mpr <| Or.inl h
    rw [← sum_format] at h
    unfold sum LOption at h
    rw [dif_neg t] at h
    rw [moves_ofSets] at h
    apply (Set.mem_union .. ).mp at h
    conv at h=> 
        left
        rw [Set.mem_range, Subtype.exists]
    conv at h=> 
        right
        rw [Set.mem_range, Subtype.exists]
    simp only [exists_prop] at h
    cases h
    case' inl h' =>left;
    case' inr h' =>right;
    all_goals 
        obtain ⟨s,⟨s1,s2⟩⟩ := h'
        use s
        exact ⟨s1,s2.symm⟩
  · intro h    
    cases h
    case' inl h'=> 
          obtain ⟨s,⟨s1,s2⟩⟩:= h'
          have t : s.option a := option_iff_lroption.mpr <| Or.inl s1
    case' inr h'=> 
          obtain ⟨s,⟨s1,s2⟩⟩:= h'
          have t : s.option b := option_iff_lroption.mpr <| Or.inl s1
    all_goals
      apply option_IsComp at t
      have t1 : ¬(IsAtom a = true ∧ IsAtom b = true) := by
        repeat rw [Atom_nComp_iff, Bool.not_eq_true]
        rw [t, Bool.true_eq_false];
        first | rw [false_and] | rw [and_false]
        rw [not_false_eq_true]
        exact True.intro
      rw [← sum_format] 
      unfold sum LOption
      rw [dif_neg t1]
      simp only [sum_format]
      rw [moves_ofSets]
      rw [(Set.mem_union .. )]      
      rw [Set.mem_range, Subtype.exists];rw [Set.mem_range, Subtype.exists]
      rw [s2]
      simp only [exists_prop]
      first 
        |{left; use s}
        |{right; use s}

lemma sum_ROption {A B : Type} {x : Primordial (A × B)} {a : Primordial A} {b : Primordial B} : x.ROption (a+b) ↔ (∃ a':Primordial A, a'.ROption a ∧ x= (a'+b)) ∨ (∃ b':Primordial B, b'.ROption b ∧ x= (a+b')) := by
  constructor
  · intro h
    have t := (not_iff_not.mpr <| sum_IsAtom).mp <| Comp_nAtom_iff.mp 
              <| option_IsComp <| option_iff_lroption.mpr <| Or.inr h
    rw [← sum_format] at h
    unfold sum ROption at h
    rw [dif_neg t] at h
    rw [moves_ofSets] at h
    apply (Set.mem_union .. ).mp at h
    conv  at h=> 
      left
      rw [Set.mem_range, Subtype.exists]
    conv at h => 
      right
      rw [Set.mem_range,Subtype.exists]
    simp only [exists_prop] at h
    cases h
    case' inl h' =>left;
    case' inr h' =>right;
    all_goals 
        obtain ⟨s,⟨s1,s2⟩⟩ := h'
        use s
        exact ⟨s1,s2.symm⟩
  · intro h
    cases h
    case' inl h'=> 
          obtain ⟨s,⟨s1,s2⟩⟩:= h'
          have t : s.option a := option_iff_lroption.mpr <| Or.inr s1
    case' inr h'=> 
          obtain ⟨s,⟨s1,s2⟩⟩:= h'
          have t : s.option b := option_iff_lroption.mpr <| Or.inr s1
    all_goals
      apply option_IsComp at t
      have t1 : ¬(IsAtom a = true ∧ IsAtom b = true) := by
        repeat rw [Atom_nComp_iff, Bool.not_eq_true]
        rw [t, Bool.true_eq_false];
        first | rw [false_and] | rw [and_false]
        rw [not_false_eq_true]
        exact True.intro
      rw [← sum_format] 
      unfold sum ROption 
      rw [dif_neg t1]
      simp only [sum_format]
      rw [moves_ofSets]
      rw [(Set.mem_union .. )]
      conv => 
        left
        rw [Set.mem_range, Subtype.exists]
      conv => 
        right
        rw [Set.mem_range, Subtype.exists]
      rw [s2]
      simp only [exists_prop]
      first 
        |{left; use s}
        |{right; use s}

lemma sum_POption {A B : Type} {x : Primordial (A × B)} {a : Primordial A} {b : Primordial B} : ∀p:Player, (x∈ (a+b).moves p ↔ (∃ a':Primordial A, a'∈ a.moves p ∧ x= (a'+b)) ∨ (∃ b':Primordial B, b'∈ b.moves p ∧ x= (a+b'))) := by
  intro p
  cases p
  · exact sum_LOption
  · exact sum_ROption

/-- if x is an option of a+b then either there exists y or z such that x= y+b or x = a+z, where y and z are options of a and b, respectively. -/
lemma sum_option {A B : Type} {x : Primordial (A × B)} {a : Primordial A} {b : Primordial B} : x.option (a+b) ↔ (∃ a':Primordial A, a'.option a ∧ x= (a'+b)) ∨ (∃ b':Primordial B, b'.option b ∧ x= (a+b')) := by
  dsimp only [option]
  simp only [Set.mem_iUnion]
  suffices (∃ i, x ∈ (a + b).moves i) ↔ ∃ i:Player, ((∃ a', (a' ∈ a.moves i) ∧ x = a' + b) ∨ ∃ b', (b' ∈ b.moves i) ∧ x = a + b') by {
        simp only [this]
        constructor
        · intro ⟨p,h⟩
          cases h
          case inl h'=>
              obtain ⟨a',ha⟩:= h'
              left
              use a'
              exact ⟨by use p;exact ha.1 ,ha.2⟩
          case inr h'=>
              obtain ⟨a',ha⟩:= h'
              right
              use a'
              exact ⟨by use p;exact ha.1 ,ha.2⟩
        ·intro h
         cases h
         case inl h' =>
           obtain ⟨a',ha⟩ := h'
           have ⟨⟨p,_⟩,_⟩:= ha
           use p
           left
           use a'
         case inr h' =>
           obtain ⟨a',ha⟩ := h'
           have ⟨⟨p,_⟩,_⟩:= ha
           use p
           right
           use a'}
--
  constructor
  · intro ⟨i,h⟩
    use i
    exact (sum_POption i).mp h
  · intro ⟨i,h⟩
    use i
    exact (sum_POption i).mpr h


/- The sum function is the same as this map when the second component is atomic. -/
private lemma old_sum_to_MAP_fst {A B : Type} (x : Primordial A) (y : Primordial B) (hy : IsAtom y) : old_sum x y =  MAP (λ a:A => (a,(Sum.getLeft (moves_or y) hy))) x := by
match hx:IsAtom x with
|true=> 
  unfold old_sum MAP
  repeat rw [dif_pos hx]
  rw [dif_pos hy]
|false =>
  unfold old_sum MAP
  rw [Bool.eq_false_iff] at hx
  rw [dif_neg hx]
  rw [dif_pos hy]
  
/-- The two sum functions agree when their second component is atomic -/  
private lemma old_sum_eq_sum_fst {A B : Type} (x : Primordial A) (y : Primordial B) (hy : IsAtom y) : old_sum x y =  x + y := by
match hx:IsAtom x with
|true =>   
  dsimp [HAdd.hAdd]
  unfold old_sum sum
  simp only [hx,  hy, and_self,↓reduceDIte]
|false =>
  dsimp [HAdd.hAdd]
  unfold old_sum sum MAP
  simp only [hx, hy,Bool.false_eq_true, and_true,↓reduceDIte, sum_format]  
  congr <;> 
  · ext p
    simp only [Set.mem_range, Subtype.exists, exists_prop, Set.mem_union]
    constructor
    · intro ⟨z,⟨ha1,ha2⟩⟩
      left
      use z
      constructor
      · exact ha1
      · rw [← old_sum_to_MAP_fst _ _ hy] at ha2
        rw [old_sum_eq_sum_fst _ _ hy] at ha2
        exact ha2
    · intro h
      match h with
      |Or.inl h' =>
          obtain ⟨a,⟨ha1,ha2⟩⟩:= h'
          use a
          constructor
          · exact ha1
          · rw [← old_sum_to_MAP_fst _ _ hy]
            rw [old_sum_eq_sum_fst _ _ hy]
            exact ha2
      |Or.inr h'=> 
          obtain ⟨b,⟨hb1,hb2⟩⟩ := h'
          exfalso
          exact isEmpty_iff.mp (Atom_no_options _ hy) ⟨b,leftORright_memMoves.mp (by cases p <;> simp only [hb1,true_or,or_true])⟩
termination_by x
decreasing_by 
  Primordial_wf

/- The sum function is the same as this map when the first component is atomic. -/
private lemma old_sum_to_MAP_snd {A B : Type} (x : Primordial A) (hx : IsAtom x) (y : Primordial B) : old_sum x y =  MAP (λ b:B => ((Sum.getLeft (moves_or x) hx),b)) y := by
match hy : IsAtom y with
|true=> 
  unfold old_sum MAP
  rw [dif_pos hx]
  repeat rw [dif_pos hy]
|false =>
  unfold old_sum MAP
  rw [Bool.eq_false_iff] at hy
  rw [dif_pos hx]
  rw [dif_neg hy]
  
/-- The two sum functions agree when their first component is atomic -/  
private lemma old_sum_eq_sum_snd {A B : Type} (x : Primordial A) (hx : IsAtom x) (y : Primordial B) : old_sum x y = x + y := by
match hy:IsAtom y with
|true => 
  dsimp [HAdd.hAdd]
  unfold old_sum sum
  simp only [hx,  hy, and_self,↓reduceDIte]
|false =>
  dsimp [HAdd.hAdd]
  unfold old_sum sum MAP
  simp only [hx, hy,Bool.false_eq_true, true_and, ↓reduceDIte, sum_format]  
  congr <;>
  · ext p
    simp only [Set.mem_range, Subtype.exists, exists_prop, Set.mem_union]
    constructor
    · intro ⟨z,⟨ha1,ha2⟩⟩
      right
      use z
      constructor
      · exact ha1
      · rw [←old_sum_to_MAP_snd _ hx _] at ha2
        rw [old_sum_eq_sum_snd _ hx _] at ha2
        exact ha2
    · intro h
      match h with
      |Or.inl h'=> 
        obtain ⟨b,⟨hb1,hb2⟩⟩ := h'
        exfalso
        exact isEmpty_iff.mp (Atom_no_options _ hx) ⟨b,leftORright_memMoves.mp (by cases p <;>simp only [hb1, true_or,or_true])⟩
      |Or.inr h' =>
        obtain ⟨a,⟨ha1,ha2⟩⟩:= h'
        use a
        constructor
        · exact ha1
        · rw [← old_sum_to_MAP_snd _ hx _]
          rw [old_sum_eq_sum_snd _ hx _]
          exact ha2
termination_by y
decreasing_by
  Primordial_wf


theorem old_sum_eq_sum {A B : Type} (x : Primordial A) (y : Primordial B) : old_sum x y = x + y := by
dsimp [HAdd.hAdd]
match hx:IsAtom x, hy:IsAtom y with
|true,true => 
    unfold old_sum sum
    simp only [hx,  hy, and_self,↓reduceDIte]
|true,false => -- x is atomic, y is composite.
    exact old_sum_eq_sum_snd _ hx _
|false,true => -- x is composite, y is atomic. 
     exact old_sum_eq_sum_fst _ _ hy
|false,false => 
  unfold old_sum sum MAP
  simp only [hx, hy,Bool.false_eq_true, and_self,↓reduceDIte]
  -- `congr` opens four goals, that prove that 
  --each of the corresponding sets are equivalent 
  --(we have {A ∪ B| C ∪ D} = {A' ∪ B'| C' ∪ D'}, 
  --so this sets out to prove that A=A',B=B', et cetera). 
  --Then `<;>` applies the tactic that follows it to each 
  --of the goals generated by `congr`.
  congr
  ext p t
  cases p 
  all_goals
    {
      conv =>
        lhs
        lhs
        conv =>
          lhs
          arg 1
          ext z
          rw [old_sum_eq_sum]
        conv =>
          rhs
          arg 1
          ext z
          rw [old_sum_eq_sum]
      dsimp [HAdd.hAdd]
      rfl}
termination_by (x,y)
decreasing_by Primordial_wf

private instance ProductAssoc {A B C : Type} : ((A×B)×C)≃(A×(B×C)):= 
  let f :((A×B)×C)→(A×(B×C)) := fun ((x1,x2),x3) => (x1,(x2,x3))
  let g :(A×(B×C))→((A×B)×C) := fun (x1,(x2,x3)) => ((x1,x2),x3)
  have hfg : f∘ g = id := by rfl;
  have hgf :  g∘f = id := by rfl;
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

private theorem sum_assoc' {A B C : Type} {a : Primordial A} {b : Primordial B} {c : Primordial.{u} C} :
MAP (fun ((x1,x2),x3) => (x1,(x2,x3))) (a + b + c) = a + (b + c) := by 
  repeat rw [← sum_format]
  unfold MAP
  cases habc : (IsAtom a)&&(IsAtom b)&&(IsAtom c)
  case true =>
    repeat rw [Bool.and_eq_true] at habc
    have this':(IsAtom a = true ∧ IsAtom (b.sum c) = true) := by 
      rw [sum_format]
      rw [sum_IsAtom]
      rw [← and_assoc]
      exact habc
    have this'':(IsAtom (a.sum b) = true ∧ IsAtom c = true) := by
      rw [sum_format]
      rw [sum_IsAtom]
      exact habc
    have this : IsAtom (sum (sum a b) c) := by 
      rw [sum_format, sum_IsAtom] at this''
      repeat rw [sum_format, sum_IsAtom]
      exact this''
    have this''':IsAtom a= true ∧ IsAtom b = true := ⟨habc.1.1,habc.1.2⟩
    have this'''':IsAtom b= true ∧ IsAtom c = true := ⟨habc.1.2,habc.2⟩
    --
    rw [dif_pos this]
    unfold sum
    rw [dif_pos (this')]
    congr
    simp_rw [dif_pos (this'')]
    unfold sum
    simp_rw [dif_pos (this''')]
    simp_rw [dif_pos (this'''')]
    rfl
  case false =>
    rw [Bool.eq_false_iff, Ne] at habc
    repeat rw [Bool.and_eq_true] at habc
    have this':¬(IsAtom a = true ∧ IsAtom (b.sum c) = true) := by 
      rw [sum_format, sum_IsAtom, ← and_assoc]
      exact habc
    have this'':¬(IsAtom (a.sum b) = true ∧ IsAtom c = true) := by 
      rw [sum_format, sum_IsAtom]
      exact habc
    have this : ¬IsAtom (sum (sum a b) c) := by 
      repeat rw [sum_format, sum_IsAtom]
      exact habc
    rw [dif_neg this]
    unfold sum
    rw [dif_neg (this')]
    congr
    ext p t
    rw [Set.mem_union]
    repeat rw [Set.mem_range]
    constructor
    · intro ⟨x,hx⟩
      have this:=(sum_POption p).mp <| x.2
      repeat rw [Subtype.exists]
      cases this 
      case inl h' => 
           obtain ⟨a',⟨ha1,ha2⟩⟩ := h'
           apply (sum_POption p).mp at ha1
           cases ha1
           case' inl h'' =>
                obtain ⟨a'',⟨ha'1,ha'2⟩⟩ := h''
                left
                use a'', ha'1
                repeat rw [sum_format]
           case' inr h'' =>
                obtain ⟨b'',⟨ha'1,ha'2⟩⟩ := h''
                right
                use b''+ c, (sum_POption p).mpr <| Or.inl ⟨b'',⟨ha'1,rfl⟩⟩
                rw [sum_format]
           -- we will need to use induction hypothesis here.
           all_goals
                rw [← sum_assoc']
                rw [← ha'2, ← ha2]
                exact hx
      case inr h' =>
           obtain ⟨c'',⟨ha1,ha2⟩⟩ := h'
           right
           use b + c'', (sum_POption p).mpr <| Or.inr ⟨c'',⟨ha1,rfl⟩⟩
           rw [sum_format]
           rw [← sum_assoc']
           conv at ha2 =>
             right
             rw [sum_format]
           rw [← ha2]
           exact hx  
    · intro h
      cases h
      case inl h' => 
        obtain ⟨⟨x,hal⟩,hx⟩ := h'
        have :((x + b) + c)∈ moves ((a+b) +c) p :=by
          rw [sum_POption]
          left
          use x + b
          constructor
          · rw [sum_POption p]
            left
            use x
          · rfl  
        use ⟨x + b + c,this⟩
        rw [sum_assoc']
        exact hx
      case inr h' => 
        obtain ⟨⟨x,hbcl⟩,hx⟩ := h'
        have : x∈ moves (b+c) p := hbcl
        rw [sum_POption] at this 
        cases this
        case inl h'' => 
          obtain ⟨b',⟨hb1,hb2⟩⟩ := h''
          have : (a+b'+c)∈ moves (a+b+c) p:= by
               rw [sum_POption]
               left
               use a + b'
               constructor
               · rw [sum_POption]
                 right
                 use b'
               · rfl
          use ⟨a + b' + c,this⟩
          rw [sum_assoc',←hb2]
          exact hx
        case inr h'' => 
          obtain ⟨c',⟨hc1,hc2⟩⟩ := h''
          have : (a+b+c')∈ moves (a+b+c) p := by
               rw [sum_POption]
               right
               use c'
          use ⟨a + b + c',this⟩
          rw [sum_assoc',←hc2]
          exact hx  
termination_by (a,b,c)
decreasing_by Primordial_wf

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

noncomputable def starGame :Primordial Bool := !{λ p => {mk_atom (pGoal p)}}

example (p : Player) : FPS starGame p := by 
  rw [FPS]
  right
  use mk_atom (pGoal p) 
  have :mk_atom (pGoal p) ∈ starGame.moves p := by 
       rw [starGame]
       simp
  use this
  rw [SPS]
  constructor
  · simp
  · have this' := Atom_no_options (mk_atom.{u} (pGoal p)) (mk_atom_IsAtom)
    intro _ _
    contradiction

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
      obtain ⟨ha,a⟩ := h'
      left
      use ha
      rw [a]
      apply pGoal_neg
    case inr h' =>
      obtain ⟨a,⟨ham,has⟩⟩ := h'
      right  
      use a
      apply not_not.mpr at has
      rw [← neg_neg p, ← fundCGT] at has
      rw [neg_neg, Classical.not_imp]
      exact ⟨ham,has⟩
  · intro h'
    cases h'
    case inl h' =>
      obtain ⟨ha,a⟩:= h'
      left 
      use ha
      by_contra 
      cases hx :(moves_or x).getLeft ha
      all_goals
          grind [= pGoal]
    case inr h' =>      
      right  
      obtain ⟨a,ham⟩ := h'
      use a
      rw [neg_neg, Classical.not_imp] at ham
      obtain ⟨ham1,ham2⟩ := ham
      use ham1
      rw [fundCGT, neg_neg p,not_not] at ham2
      exact ham2
termination_by x
decreasing_by Primordial_wf

theorem fundCGTv2 (x : Primordial Bool) : ∀ p, SPS x p ↔ ¬ (FPS x (-p)):= by 
  intro p
  have :=(fundCGT x (-p)).symm
  rw [neg_neg, ← not_iff, Classical.not_iff] at this
  exact iff_not_comm.mp (id (Iff.symm this))

abbrev oc (x : Primordial Bool) : Prop × Prop := (FPS x left, SPS x left)

abbrev eval {A B : Type} {p : (A → B) → Prop} (xf : A × {f:A → B| p f}) : B := xf.2.1 xf.1 


end Primordial

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




-- def D := Unit
-- def z:Unit := Unit.unit





