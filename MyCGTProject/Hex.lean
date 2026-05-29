-- This is code that describes a lot of the operations on games of Hex.
import Mathlib.Logic.Small.Set
import Mathlib.Data.Set.Image
import Mathlib.Data.Set.Basic
import Mathlib.Order.OrderDual
--import MyCGTProject.Primordial
import MyCGTProject.Basic
--import Mathlib.Order.GameAdd
set_option linter.style.lambdaSyntax false
set_option linter.style.longLine false
set_option linter.unnecessarySeqFocus false
--set_option trace.Meta.synthInstance true

universe u

open Primordial

mutual


/-- this is obviosly not an ideal way of defining leq, but it is necessary to convince lean that the functions are mutually recursive. this is because of the weird way in which lean handles mutual recursion. -/
def intrRel.leq {A : Type} [Preorder A] (g k : Primordial.{u} A) : Prop := 
((∀ l∈ gᴸ, intrRel.tri l k) ∧ 
(∀ r∈ kᴿ, intrRel.tri g r)) ∧ 
(IsAtom g=true∨IsAtom k=true →  intrRel.tri g k)
termination_by ((g,k),1)
decreasing_by Primordial_wf

def intrRel.tri {A : Type} [Preorder A] (g k : Primordial.{u} A) : Prop := 
((∃ r, ∃ _:r∈ gᴿ, intrRel.leq r k) ∨
(∃l,∃ _: l∈ kᴸ, intrRel.leq g l)) ∨
∃ hg: IsAtom g, ∃ hk : IsAtom k, Sum.getLeft (moves_or g) hg ≤ Sum.getLeft (moves_or k) hk
termination_by ((g,k),0)
decreasing_by Primordial_wf

end

instance {A : Type} [Preorder A] : LE (Primordial A) where
le := intrRel.leq

@[simp]
lemma intrRel.leq.format {A : Type} [Preorder A] (g h : Primordial.{u} A) : intrRel.leq g h ↔ g≤h := by rfl

-- this symbol is called "WHITE LEFT POINTING SMALL TRIANGLE" in unicode, hex is ???
notation g:max "◃" h:max => intrRel.tri g h


lemma intrRel.leq.simp {A : Type} [Preorder A] {g h : Primordial.{u} A} : g≤ h ↔ 
((∀ l∈ gᴸ, intrRel.tri l h) ∧ 
(∀ r∈ hᴿ, intrRel.tri g r)) ∧ 
(IsAtom g=true∨IsAtom h=true → g◃h) := by  
  rw [← intrRel.leq.format,leq]

lemma intrRel.leq.refl {A : Type} [Preorder A] (g : Primordial.{u} A) : g ≤ g:= by
  rw [leq.simp]
  have t1: ∀ l ∈ gᴸ, tri l g := by
       intro l hl
       rw [tri]
       left; right
       use l, hl
       exact intrRel.leq.refl l
  have t2: ∀ r ∈ gᴿ, tri g r := by
       intro r hr
       rw [tri]
       left;left
       use r, hr
       exact intrRel.leq.refl r
  have t3: IsAtom g = true∨ IsAtom g = true → g◃g  := by 
       intro h
       rw [or_self] at h
       rw [tri]
       right
       use h, h
  exact ⟨⟨t1,t2⟩,t3⟩
termination_by g
decreasing_by Primordial_wf

lemma forall_Atom {A : Type} {g : Primordial A} (hg : IsAtom g) (p : Player) {q : Primordial A → Prop} : (∀ g' ∈ moves g p, q g')↔ True := by
      have : IsEmpty (Subtype (λ x => x∈ moves g p)) := by
         rw [Set.isEmpty_coe_sort, moves]
         rw [dif_neg (Atom_nComp_iff.mp hg)]
      rw [← @Subtype.forall _ _ (λ x => q x.1)]
      rw [IsEmpty.forall_iff]

lemma exists_Atom {A : Type} {g : Primordial A} (hg : IsAtom g) (p : Player) {q : Primordial A → Prop} : (∃ g' ∈ moves g p, q g')↔ False := by
      simp [forall_Atom hg]

lemma atomic_leq {A : Type} [Preorder A] (g k : Primordial.{u} A) (hg : IsAtom g) (hk : IsAtom k) : Sum.getLeft (moves_or g) hg ≤ Sum.getLeft (moves_or k) hk ↔ g≤ k:= 
      by
      constructor
      · intro h
        rw [intrRel.leq.simp]
        constructor
        · simp [forall_Atom hg,forall_Atom hk]
        · intro _  
          rw [intrRel.tri]
          right
          use hg, hk
      · intro hgk
        rw [intrRel.leq.simp] at hgk
        apply And.right at hgk
        specialize hgk <| Or.inl hg
        rw [intrRel.tri] at hgk
        simp only [intrRel.leq.format] at hgk
        cases hgk
        case inl ht => 
            simp [exists_Atom hg, exists_Atom hk] at ht
        case inr ha => 
               obtain ⟨_,_,h⟩ := ha
               assumption

/-- this defines the `gᵒᵖ` notation, which makes talking about the opposite of a game much easier. I suppose I could have made this an instance of the negation notation. This allows you to not think about what the opposite of a poset is in mathlib. -/
noncomputable abbrev op {A : Type} [Preorder A] (g : Primordial A) := @Dual Aᵒᵈ g
notation g:max "ᵒᵖ" => op g


-- duality lemmas for leq and tri.
mutual
lemma leq_Dual' {A : Type} [Preorder A] (g k : Primordial A) : g ≤ k → (kᵒᵖ ≤ gᵒᵖ) := by
  intro h
  rw [intrRel.leq.simp]
  have hl : ∀ l ∈ (kᵒᵖ)ᴸ, l◃ (gᵒᵖ) := by 
       intro l hl
       have :(lᵒᵖ) ∈ kᴿ  := by 
            have := Dual_option hl
            rw [Dual_selfInverse] at this
            assumption
       rw [intrRel.leq.simp] at h
       apply And.left at h
       apply And.right at h
       specialize h (lᵒᵖ) this
       apply tri_Dual' at h
       repeat rw [op] at h
       rw [Dual_selfInverse] at h
       assumption 
  have hr : ∀ r ∈ (gᵒᵖ)ᴿ, (kᵒᵖ)◃ r := by 
       intro r hr
       have :(rᵒᵖ) ∈ gᴸ  := by 
            have := Dual_option hr
            rw [Dual_selfInverse] at this
            assumption
       rw [intrRel.leq.simp] at h
       apply And.left at h
       apply And.left at h
       specialize h (rᵒᵖ) this
       apply tri_Dual' at h
       repeat rw [op] at h
       rw [Dual_selfInverse] at h
       assumption 
  have ha : IsAtom k.Dual = true ∨ IsAtom g.Dual = true → (kᵒᵖ)◃(gᵒᵖ) := by 
    intro h'
    rw [intrRel.leq.simp] at h
    apply And.right at h
    rw [← @Dual_IsAtom _ g, ← @Dual_IsAtom _ k] at h
    specialize h (h'.symm)
    exact tri_Dual' _ _ h
  exact ⟨⟨hl,hr⟩,ha⟩
termination_by (g,k, 1)
decreasing_by Primordial_wf

lemma tri_Dual' {A : Type} [ t : Preorder A] (g k : Primordial A) : g ◃ k → ((kᵒᵖ) ◃ (gᵒᵖ)) := by
  intro h
  rw [intrRel.tri] at h
  cases h
  case inl hc=>
    cases hc
    case inl hr =>
      obtain ⟨r,hr,h'⟩:= hr
      have : (rᵒᵖ) ∈ (gᵒᵖ)ᴸ := Dual_option hr
      rw [intrRel.leq.format] at h'
      apply leq_Dual' at h'
      rw [intrRel.tri]
      left ; right
      use r.Dual, this
      rw [intrRel.leq.format]
      exact h'
    case inr hl =>
      obtain ⟨l,hl,h'⟩:= hl
      have : (lᵒᵖ) ∈ (kᵒᵖ)ᴿ := Dual_option hl
      rw [intrRel.leq.format] at h'
      apply leq_Dual' at h'
      rw [intrRel.tri]
      left ; left
      use l.Dual, this
      rw [intrRel.leq.format]
      exact h'
  case inr ha=>
    obtain ⟨hg,hk,hgk⟩ := ha
    have hk' :IsAtom k.Dual = true := by 
         rw [Dual_IsAtom]
         exact hk
    have hg' :IsAtom g.Dual = true := by 
         rw [Dual_IsAtom]
         exact hg
    have tk :kᵒᵖ = k := by
         unfold Dual
         erw [if_pos hk]
    have tg :gᵒᵖ = g := by 
         unfold Dual
         erw [if_pos hg]
    rw [tk,tg]
    rw [intrRel.tri]
    right
    use hk, hg
    assumption
    
termination_by (g,k, 0)
decreasing_by Primordial_wf
end

/-- Duality theorems for `leq` -/
theorem leq_Dual {A : Type} [t : Preorder A] (g k : Primordial A) : g ≤ k ↔ (kᵒᵖ ≤ gᵒᵖ) := 
  by
  constructor
  · exact leq_Dual' g k
  · intro h
    apply leq_Dual' at h
    dsimp [op] at h
    repeat erw [Dual_selfInverse] at h
    assumption

/-- Duality theorems for `tri` -/
theorem tri_Dual {A : Type} [t : Preorder A] (g k : Primordial A) : g ◃ k ↔ ((kᵒᵖ) ◃ (gᵒᵖ)) := 
  by
  constructor
  · exact tri_Dual' g k
  · intro h
    apply tri_Dual' at h
    dsimp [op] at h
    repeat erw [Dual_selfInverse] at h
    assumption

-- a proof of transitivity
mutual

lemma intrRel.transtl {A : Type} [Preorder A] (g j k : Primordial.{u} A) : (g ◃ j) → (j ≤ k) → (g ◃ k) := by
  intro h1 h2
  rw [tri] at h1
  cases h1
  case inl h' => 
    cases h'
    case inl h'' =>
      rw [tri]
      left;left
      obtain ⟨r,hr,hrj⟩ := h''
      use r, hr
      exact intrRel.trans _ _ _ hrj h2 
    case inr h''=> 
      obtain ⟨l,hl,hgl⟩ := h''
      rw [leq.simp] at h2
      apply And.left at h2
      apply And.left at h2
      specialize h2 l hl
      exact intrRel.translt _ _ _ hgl h2
  case inr h' => 
      obtain ⟨hg,hj,c⟩ := h'
      rw [leq.simp] at h2
      have :j◃k := by 
        exact (And.right h2) (Or.inl hj)
      rw [tri] at this
      cases this
      case inl ht => 
           conv at ht =>
             left
             simp [exists_Atom hj]
           rw [false_or] at ht
           obtain ⟨l,hl,hjl⟩:= ht
           rw [← leq.simp] at h2
           have this'': g ≤ j := (atomic_leq .. ).mp c
           have := intrRel.trans _ _ _ this'' hjl
           rw [tri]
           left;right
           use l, hl
           exact this
      case inr ht => 
           obtain ⟨_,hk,d⟩:= ht
           rw [tri]
           right
           use hg, hk
           grind only
termination_by ((g,j,k),0)
decreasing_by Primordial_wf

lemma intrRel.translt {A : Type} [Preorder A] (g j k : Primordial.{u} A) : (g ≤ j) → (j ◃ k) → (g ◃ k) := by
  intro h1 h2
  rw [tri] at h2
  cases h2
  case inl h' =>
      cases h'
      case inl h'' =>
           rw [← intrRel.leq.format,leq] at h1
           apply And.left at h1
           apply And.right at h1
           obtain ⟨l,hl,hlk⟩ := h''
           specialize h1 l hl
           exact intrRel.transtl _ _ _ h1 hlk
      case inr h'' =>
           rw [tri]
           left;right
           obtain ⟨l,hl,hjl⟩ := h''
           use l, hl
           exact intrRel.trans _ _ _ h1 hjl
  case inr h' => 
      obtain ⟨hj,hk,c⟩ := h'
      rw [leq.simp] at h1
      have :g◃j := (And.right h1) (Or.inr hj)
      rw [tri] at this
      conv at this =>
             left;right
             simp [exists_Atom hj]
      rw [or_false] at this
      cases this
      case inl ht => 
           obtain ⟨l,hl,hjl⟩:= ht
           have this'': j ≤ k := (atomic_leq .. ).mp c
           have := intrRel.trans _ _ _ hjl this''
           rw [tri]
           left;left
           use l, hl
           exact this
      case inr ht => 
           obtain ⟨hg,_,d⟩:= ht
           rw [tri]
           right
           use hg, hk
           grind only
termination_by ((g,j,k),0)
decreasing_by Primordial_wf

lemma intrRel.trans {A : Type} [Preorder A] (g j k : Primordial.{u} A) : (g ≤ j) → (j ≤ k) → (g ≤ k):= by
  intro h1 h2
  rw [leq.simp]
  have t1: ∀ l ∈ gᴸ, tri l k := by
       rw [← intrRel.leq.format,leq] at h1
       obtain ⟨⟨h,_⟩,_⟩ := h1
       intro l hl
       specialize h l hl
       exact intrRel.transtl _ _ _ h h2
  have t2: ∀ r ∈ kᴿ, tri g r := by 
       rw [← intrRel.leq.format,leq] at h2
       obtain ⟨⟨_,h⟩,_⟩ := h2
       intro r hr
       specialize h r hr
       exact intrRel.translt _ _ _ h1 h
  have t3: IsAtom g = true∨ IsAtom k = true → g◃k  := by 
       intro h
       cases h
       case inl h' =>
            rw [leq.simp] at h1
            exact intrRel.transtl _ _ _ ((And.right h1) (Or.inl h')) h2
       case inr h' => 
            rw [leq.simp] at h2
            exact intrRel.translt _ _ _ h1 ((And.right h2) (Or.inr h')) 
  exact ⟨⟨t1,t2⟩,t3⟩
termination_by ((g,j,k),1)
decreasing_by Primordial_wf
end


instance {A : Type} [Preorder A] : Preorder (Primordial A) where
le_refl := intrRel.leq.refl
le_trans := intrRel.trans

abbrev intrRel.eq {A : Type} [Preorder A] (g k : Primordial A) : Prop := g≤ k ∧ k≤ g
@[refl]
lemma intrEq.refl {A : Type} [Preorder A] : ∀ (x : Primordial A), intrRel.eq x x := by simp

@[symm]
lemma intrEq.symm {A : Type} [Preorder A] : ∀ {x y : Primordial A}, intrRel.eq x y ↔ intrRel.eq y x := by grind

instance intrEq {A : Type} [Preorder A] : Equivalence (@intrRel.eq A _) where
refl := intrEq.refl
symm  := intrEq.symm.mp
trans := by grind

notation g:max "≃" k:max => intrRel.eq g k

theorem eq_Dual {A : Type} [t : Preorder A] (g k : Primordial A) : g ≃ k ↔ ((kᵒᵖ) ≃ (gᵒᵖ)) := by 
  repeat rw [intrRel.eq]
  rw [leq_Dual g k]
  rw [leq_Dual k g]


lemma lemma_4_8_left {A : Type} [Preorder A] {L R : Set (Primordial A)} [Small.{u} L] [Small.{u} R] {k k' : Primordial A} (hk : k ≤ k') : !{insert k L|R} ≤ !{insert k' L|R} := by
      rw [intrRel.leq.simp]
      have tk  := ofSets_IsComp <| Player.cases (insert k L) R
      have tk' := ofSets_IsComp <| Player.cases (insert k' L) R
      rw [Comp_nAtom_iff] at tk tk'
      refine ⟨?_,by simp_all⟩
      constructor <;> {intro g;rw [intrRel.tri];aesop}

-- the first experiment in proving something by duality. it was a pain in the **** but it worked! I would like to make the process less painful in the future...
lemma lemma_4_8_right {A : Type} [Preorder A] {L R : Set (Primordial A)} [Small.{u} L] [Small.{u} R] {k k' : Primordial A} (hk : k ≤ k') : !{L| insert k R} ≤ !{L| insert k' R} := by
  rw [leq_Dual] at hk ⊢
  dsimp [op]
  erw [@Dual_ofSets Aᵒᵈ L (insert k' R)]
  erw [@Dual_ofSets Aᵒᵈ L (insert k  R)]
  simp only [Set.range_insert]
  exact @lemma_4_8_left _ _ (Set.range fun (y : R) ↦ @Dual Aᵒᵈ (y.1)) (Set.range fun (y : L) ↦ @Dual Aᵒᵈ y.1) _ _ _ _ hk

lemma lemma_4_9_left {A : Type} [Preorder A] {L R : Set (Primordial A)} [Small.{u} L] [Small.{u} R] {k : Primordial A} : !{L|R}≤!{insert k L|R} := by 
      rw [intrRel.leq.simp]
      have tk  := ofSets_IsComp <| Player.cases (insert k L) R
      have tk' := ofSets_IsComp <| Player.cases  L R
      refine ⟨?_,by simp_all⟩
      constructor <;> {intro g;rw [intrRel.tri];aesop}

lemma lemma_4_9_right {A : Type} [Preorder A] {L R : Set (Primordial A)} [Small.{u} L] [Small.{u} R] {k : Primordial A} : !{L|insert k R}≤!{L|R} := by 
      rw [intrRel.leq.simp]
      have tk  := ofSets_IsComp <| Player.cases L R
      have tk' := ofSets_IsComp <| Player.cases L (insert k R)
      refine ⟨?_,by simp_all⟩
      constructor <;> {intro g;rw [intrRel.tri];aesop}

lemma giftHorse_left {A : Type} [Preorder A] {L R : Set (Primordial A)} [Small.{u} L] [Small.{u} R] {k : Primordial A} : k◃ !{L|R}↔ !{L|R}≃!{insert k L|R} := by 
      have : k◃ !{insert k L|R} := by rw [intrRel.tri];aesop
      have mpr : !{L|R}≃!{insert k L|R}→ k◃ !{L|R} := by
             intro h
             rw [intrRel.eq] at h
             exact intrRel.transtl _ _ _ this h.right
      have mp : k◃ !{L|R}→ !{L|R}≃!{insert k L|R} := by
             intro h
             rw [intrRel.eq]
             refine ⟨lemma_4_9_left,?_⟩
             rw [intrRel.leq.simp]
             have tk :=ofSets_IsComp <| Player.cases (insert k L) R
             have tk' := ofSets_IsComp <| Player.cases L R
             refine ⟨?_, by simp_all⟩
             constructor 
             · intro g hg; rw [moves_ofSets, Player.cases, Set.mem_insert_iff] at hg
               cases hg
               case inl h' => aesop
               case inr h' => rw [intrRel.tri]; aesop
             · intro g hg;rw [intrRel.tri]; aesop
      exact ⟨mp,mpr⟩

lemma giftHorse_right {A : Type} [Preorder A] {L R : Set (Primordial A)} [Small.{u} L] [Small.{u} R] {k : Primordial A} : !{L|R}◃k↔ !{L|R}≃!{L|insert k R} := by 
      rw [tri_Dual, eq_Dual,intrEq.symm]
      repeat rw [op]
      erw [@Dual_ofSets Aᵒᵈ L (insert k R)]
      repeat erw [@Dual_ofSets Aᵒᵈ L R]
      simp only [Set.range_insert, giftHorse_left]












--contextual order on games
def contxRel {A : Type} [Preorder A] (g h : Primordial.{u} A) : Prop := ∀ x : Primordial.{u} ({f : A → Bool | Monotone f}), oc (MAP eval (g + x)) ≤ oc (MAP eval (h + x))

-- The notation `≤ᶜ` for contextual relation. I do not know if this is optimal, but it will suffice.
notation g:max "≤ᶜ" h:max => contxRel g h




