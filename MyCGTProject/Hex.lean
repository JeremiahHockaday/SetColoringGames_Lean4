-- This is code that describes a lot of the operations on games of Hex.
import Mathlib.Logic.Small.Set
import Mathlib.Data.Set.Image
import Mathlib.Data.Set.Basic
--import MyCGTProject.Primordial
import MyCGTProject.Basic
--import Mathlib.Order.GameAdd
set_option linter.style.lambdaSyntax false
set_option linter.style.longLine false
set_option linter.unnecessarySeqFocus false
--set_option trace.Meta.synthInstance true

universe u

open Primordial

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



mutual

/-- this is obviosly not an ideal way of defining leq, but it is necessary to convince lean that the functions are mutually recursive. this is because of the weird way in which lean handles mutual recursion. -/
def intrRel.leq {A : Type} [Preorder A] (g h : Primordial.{u} A) : Prop := 
((∀ l∈ gᴸ, intrRel.tri l h) ∧ 
(∀ r∈ hᴿ, intrRel.tri g r)) ∧ 
(IsAtom g=true∨IsAtom h=true →  
  ((∃ r, ∃ _:r∈ gᴿ, intrRel.leq r h) ∨ 
  (∃l,∃ _: l∈ hᴸ, intrRel.leq g l)) ∨ 
  ∃ hg: IsAtom g, ∃ hh : IsAtom h, Sum.getLeft (moves_or g) hg ≤ Sum.getLeft (moves_or h) hh)
termination_by (g,h)
decreasing_by Primordial_wf

def intrRel.tri {A : Type} [Preorder A] (g h : Primordial.{u} A) : Prop := 
((∃ r, ∃ _:r∈ gᴿ, intrRel.leq r h) ∨ 
(∃l,∃ _: l∈ hᴸ, intrRel.leq g l)) ∨ 
∃ hg: IsAtom g, ∃ hh : IsAtom h, Sum.getLeft (moves_or g) hg ≤ Sum.getLeft (moves_or h) hh
termination_by (g,h)
decreasing_by Primordial_wf
-- (IsAtom g=true∨IsAtom h=true →  intrRel.tri g h)
-- termination_by ((g,h),1)



end

instance {A : Type} [Preorder A] : LE (Primordial A) where
le := intrRel.leq

lemma intrRel.leq.format {A : Type} [Preorder A] (g h : Primordial.{u} A) : intrRel.leq g h ↔ g≤h := by rfl

-- this symbol is called "WHITE LEFT POINTING SMALL TRIANGLE" in unicode, hex is ???
notation g:max "◃" h:max => intrRel.tri g h


@[simp]
lemma intrRel.leq.simp {A : Type} [Preorder A] {g h : Primordial.{u} A} : g≤ h ↔ 
((∀ l∈ gᴸ, intrRel.tri l h) ∧ 
(∀ r∈ hᴿ, intrRel.tri g r)) ∧ 
(IsAtom g=true∨IsAtom h=true → g◃h) := by 
  rw [← intrRel.leq.format,leq]
  repeat rw [and_congr_right_iff]
  intro _
  rw [tri]
  

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

lemma atomic_leq {A : Type} [Preorder A] (g k : Primordial.{u} A) (hg : IsAtom g) (hk : IsAtom k) : Sum.getLeft (moves_or g) hg ≤ Sum.getLeft (moves_or k) hk → g≤ k:= 
      have thisR : IsEmpty (Subtype (λ x => x∈ kᴿ)):= by
                rw [Set.isEmpty_coe_sort]
                rw [moves]
                rw [dif_neg (Atom_nComp_iff.mp hk)]
      have thisL : IsEmpty (Subtype (λ x => x∈ gᴸ)):= by
                rw [Set.isEmpty_coe_sort]
                rw [moves]
                rw [dif_neg (Atom_nComp_iff.mp hg)]
      by
      intro h
      rw [intrRel.leq.simp]
      constructor
      · rw [← @Subtype.forall _ _ (λ x => x.1 ◃ k)]
        rw [← @Subtype.forall _ _ (λ x => g ◃ x.1)]
        repeat rw [IsEmpty.forall_iff]
        simp
      · intro _  
        rw [intrRel.tri]
        right
        use hg, hk


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
      have thisR : IsEmpty (Subtype (λ x => x∈ jᴿ)):= by
                rw [Set.isEmpty_coe_sort]
                rw [moves]
                rw [dif_neg (Atom_nComp_iff.mp hj)]
      cases this
      case inl ht => 
           conv at ht =>
             left
             rw [← @Subtype.exists _ _ (λ x => leq x.1 k)]
             rw [@IsEmpty.exists_iff _ thisR]
           rw [false_or] at ht
           obtain ⟨l,hl,hjl⟩:= ht
           rw [← leq.simp] at h2
           have this'': g ≤ j := atomic_leq _ _ _ _ c
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
termination_by (g,j,k)
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
      have :g◃j := by
        exact (And.right h1) (Or.inr hj)
      rw [tri] at this
      have thisL : IsEmpty (Subtype (λ x => x∈ jᴸ)):= by
                rw [Set.isEmpty_coe_sort]
                rw [moves]
                rw [dif_neg (Atom_nComp_iff.mp hj)]
      conv at this =>
             left;right
             rw [← @Subtype.exists _ _ (λ x => leq g x.1)]
             rw [@IsEmpty.exists_iff _ thisL]
      rw [or_false] at this
      cases this
      case inl ht => 
           obtain ⟨l,hl,hjl⟩:= ht
           have this'': j ≤ k := atomic_leq _ _ _ _ c
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
termination_by (g,j,k)
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
            have thisR : IsEmpty (Subtype (λ x => x∈ gᴿ)):= by
                rw [Set.isEmpty_coe_sort]
                rw [moves]
                rw [dif_neg (Atom_nComp_iff.mp h')]
            rw [leq.simp] at h1
            apply And.right at h1
            specialize h1 (Or.inl h')
            rw [tri] at h1
            conv at h1 =>
                 left;left
                 rw [← @Subtype.exists _ _ (λ x => leq x.1 j)]
                 rw [@IsEmpty.exists_iff _ thisR]
            rw [false_or] at h1
            rw [← intrRel.leq.format,leq] at h2
            cases h1
            case inl hl =>
                 apply And.left at h2
                 apply And.left at h2
                 obtain ⟨l,hl,hjl⟩:= hl
                 specialize h2 l hl
                 exact intrRel.translt _ _ _ hjl h2
            case inr hr =>
                 apply And.right at h2
                 obtain ⟨hg,hj,hgj⟩ := hr
                 have thisR' : IsEmpty (Subtype (λ x => x∈ jᴿ)):= by
                      rw [Set.isEmpty_coe_sort]
                      rw [moves]
                      rw [dif_neg (Atom_nComp_iff.mp hj)]
                 specialize h2 (Or.inl hj)
                 
                 conv at h2 =>
                      left;left
                      rw [← @Subtype.exists _ _ (λ x => leq x.1 k)]
                      rw [@IsEmpty.exists_iff _ thisR']
                 rw [false_or] at h2
                 cases h2
                 case inl h'' =>
                      obtain ⟨l,hl,hjl⟩:= h''
                      have this'': g ≤ j := atomic_leq _ _ _ _ hgj
                      have := intrRel.trans _ _ _ this'' hjl
                      rw [tri]
                      left;right
                      use l, hl
                      exact this
                 case inr h'' =>
                   obtain ⟨_,hk,t⟩:= h''
                   rw [tri]
                   right
                   use hg, hk
                   grind only
            -- mutual tries to force each call to decrease, making the following line break... this should not happen, it is weird that it does.
            --exact intrRel.transtl _ _ _ h1 h2
       case inr h' => 
            have thisR : IsEmpty (Subtype (λ x => x∈ kᴸ)):= by
                rw [Set.isEmpty_coe_sort]
                rw [moves]
                rw [dif_neg (Atom_nComp_iff.mp h')]
            rw [leq.simp] at h2
            apply And.right at h2
            specialize h2 (Or.inr h')
            rw [tri] at h2
            conv at h2 =>
                 left; right
                 rw [← @Subtype.exists _ _ (λ x => leq j x.1)]
                 rw [@IsEmpty.exists_iff _ thisR]
            rw [or_false] at h2
            rw [← intrRel.leq.format,leq] at h1
            cases h2
            case inl hl =>
                 apply And.left at h1
                 apply And.right at h1
                 obtain ⟨l,hl,hjl⟩:= hl
                 specialize h1 l hl
                 exact intrRel.transtl _ _ _ h1 hjl
            case inr hr =>
                 apply And.right at h1
                 obtain ⟨hj,hk,hjk⟩ := hr
                 have thisL' : IsEmpty (Subtype (λ x => x∈ jᴸ)):= by
                      rw [Set.isEmpty_coe_sort]
                      rw [moves]
                      rw [dif_neg (Atom_nComp_iff.mp hj)]
                 specialize h1 (Or.inr hj)
                 
                 conv at h1 =>
                      left;right
                      rw [← @Subtype.exists _ _ (λ x => leq g x.1)]
                      rw [@IsEmpty.exists_iff _ thisL']
                 rw [or_false] at h1
                 cases h1
                 case inl h'' =>
                      obtain ⟨r,hr,hjr⟩:= h''
                      have this'': j≤ k := atomic_leq _ _ _ _ hjk
                      have := intrRel.trans _ _ _ hjr this''
                      rw [tri]
                      left;left
                      use r, hr
                      exact this
                 case inr h'' =>
                   obtain ⟨hg,_,t⟩:= h''
                   rw [tri]
                   right
                   use hg, hk
                   grind only
  exact ⟨⟨t1,t2⟩,t3⟩
termination_by (g,j,k)
decreasing_by Primordial_wf
end

--instance {A : Type} [Preorder A] : Preorder (Primordial A) where
abbrev oc (x : Primordial Bool) : Prop × Prop := (FPS x left, SPS x left)

abbrev eval {A B : Type} {p : (A → B) → Prop} (xf : A × {f:A → B| p f}) : B := xf.2.1 xf.1 

--contextual order on games
def contxRel {A : Type} [Preorder A] (g h : Primordial.{u} A) : Prop := ∀ x : Primordial.{u} ({f : A → Bool | Monotone f}), oc (MAP eval (g + x)) ≤ oc (MAP eval (h + x))






-- The notation `≤ᶜ` for contextual relation. I do not know if this is optimal, but it will suffice.
notation g:max "≤ᶜ" h:max => contxRel g h




-- need to generalize this, do not want a left and right version? should be able to supply a player p and get the corresponding theorem, not sure how to express that...
-- lemma giftHorseL {A : Type} [Preorder A] {s t gs : Set (Primordial.{u} A)} [Small.{u} s] [Small.{u} t] [Small.{u} gs] : !{s|t} ≤ !{s∪gs|t} :=


-- !{s|t∪gs} ≤ !{s|t}
