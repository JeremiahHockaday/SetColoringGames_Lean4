/-
Copyright (c) 2025 Violeta Hernández Palacios. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Violeta Hernández Palacios
-/
module

public import Mathlib.Logic.Small.Defs
public import Mathlib.Logic.Small.Set

import Mathlib.Logic.Relation
import Mathlib.Order.SetNotation
import Mathlib.Data.Set.Image
import Mathlib.Data.Set.Basic


set_option linter.style.longLine false
set_option linter.unnecessarySeqFocus false

universe u

public section

instance small_isEmpty {α : Type (u + 1)} [IsEmpty α] : Small.{u} α := by 
  let f : α→Unit := fun _ => Unit.unit;
  infer_instance;

@[reducible]
noncomputable def nonempty_codomain {α β} (f : α → β) [inst : Nonempty α] : Nonempty β := 
let x := Classical.choice (inst);
Nonempty.intro (f x)

@[reducible]
noncomputable def Nonempty_equiv {α} {β} [inst : Nonempty α] (h : Equiv α β) : Nonempty β := nonempty_codomain (Equiv.toFun h)

@[reducible]
noncomputable def nonempty_range {α β} (f : α → β) (X : Set α) (hx : X.Nonempty) : (Set.image f X).Nonempty := by
  rcases hx with ⟨b,hb⟩
  have h : Set.image f X (f b) := by 
    dsimp [Set.image]
    use b
  use (f b) 
  use b  

------------------
def sub_temp_left {α : Type (u + 1)} (p : α → Prop) (X : Set (Subtype p)) : X→ Set.image Subtype.val X := fun x => ⟨x.val, by 
    let ⟨⟨a,ha⟩,hy⟩ := x;
    simp only [Set.mem_image, Subtype.exists, exists_and_right, exists_eq_right]
    constructor
    · exact hy
    · exact ha 
    ⟩

def sub_temp_right {α : Type (u + 1)} (p : α → Prop) (X : Set (Subtype p)) : Set.image Subtype.val X → X := fun x => ⟨⟨x.val, by 
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

lemma subtype_set_small {α : Type (u + 1)} (p : α → Prop) (X : Set (Subtype p)) [Small.{u} X] : Small.{u} (Set.image Subtype.val X):= by 
  let f := sub_temp_left p X;
  have hg : Function.Injective (sub_temp_right p X) := by
    intro b c hi
    simp only [sub_temp_right,Subtype.mk.injEq] at hi
    ext 
    rw [hi]
  exact small_of_injective (hg)

-------------------
variable {α : Type*} (r : α → α → Prop) [H : ∀ x, Small.{u} {y // r x y}]

private def level [∀ x, Small.{u} {y // r x y}] (x : α) : ℕ → Set α
  | 0 => {x}
  | n + 1 => ⋃₀ ((fun x ↦ {y | r x y}) '' level x n)

private theorem small_level (x : α) : ∀ n, Small.{u} (level r x n)
  | 0 => small_single _
  | n + 1 => by
    refine @small_sUnion _ _ ?_ ?_
    · have := small_level x n
      exact small_image ..
    · simp_all

private theorem small_sUnion_level (x : α) : Small.{u} (⋃₀ Set.range (level r x)) := by
  refine @small_sUnion _ _ ?_ ?_
  · exact small_range ..
  · simp [small_level]

instance small_transGen (x : α) : Small.{u} {y // Relation.TransGen r x y} := by
  refine @small_subset _ _ _ (fun y hy ↦ ?_) (small_sUnion_level r x)
  simp_rw [Set.mem_sUnion, Set.mem_range, exists_exists_eq_and]
  induction hy with
  | single =>
    use 1
    simpa [level]
  | tail hy hr IH =>
    obtain ⟨n, hn⟩ := IH
    use n + 1
    simpa [level] using ⟨_, hn, hr⟩

instance small_transGen' [∀ x, Small.{u} {y // r y x}] (x : α) :
    Small.{u} {y // Relation.TransGen r y x} := by
  simp_rw [← Relation.transGen_swap (r := r)]
  infer_instance

instance small_reflTransGen (x : α) : Small.{u} {y // Relation.ReflTransGen r x y} := by
  simp_rw [Relation.reflTransGen_iff_eq_or_transGen]
  exact @small_insert _ _ _ (small_transGen ..)

instance small_reflTransGen' [∀ x, Small.{u} {y // r y x}] (x : α) :
    Small.{u} {y // Relation.ReflTransGen r y x} := by
  simp_rw [← Relation.reflTransGen_swap (r := r)]
  infer_instance
