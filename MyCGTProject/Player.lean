/-
Copyright (c) 2025 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
module 

public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Logic.Small.Defs

import Mathlib.Tactic.DeriveFintype
set_option linter.style.longLine false

/-!
# Type of players

This file implements the two-element type of players (`Left`, `Right`), alongside other basic
notational machinery to be used within game theory.
-/

@[expose] public section

universe u

/-! ### Players -/

/-- Either the Left or Right player. -/
@[aesop safe cases, grind cases]
inductive Player where
  /-- The Left player. -/
  | left  : Player
  /-- The Right player. -/
  | right : Player
deriving DecidableEq, Fintype, Inhabited

namespace Player

/-- Specify a function `Player → α` from its two outputs. -/
@[simp]
abbrev cases {α : Sort*} (l r : α) : Player → α
  | left => l
  | right => r

lemma apply_cases {α β : Sort*} (f : α → β) (l r : α) (p : Player) :
    f (cases l r p) = cases (f l) (f r) p := by
  cases p <;> rfl

@[simp]
theorem cases_inj {α : Sort*} {l₁ r₁ l₂ r₂ : α} :
    cases l₁ r₁ = cases l₂ r₂ ↔ l₁ = l₂ ∧ r₁ = r₂ :=
  ⟨fun h ↦ ⟨congr($h left), congr($h right)⟩, fun ⟨hl, hr⟩ ↦ hl ▸ hr ▸ rfl⟩

theorem const_of_left_eq_right {α : Sort*} {f : Player → α} (hf : f left = f right) :
    ∀ p q, f p = f q
  | left, left | right, right => rfl
  | left, right => hf
  | right, left => hf.symm

theorem const_of_left_eq_right' {f : Player → Prop} (hf : f left ↔ f right) (p q) : f p ↔ f q :=
  (const_of_left_eq_right hf.eq ..).to_iff

@[simp]
protected lemma «forall» {p : Player → Prop} :
    (∀ x, p x) ↔ p left ∧ p right :=
  ⟨fun h ↦ ⟨h left, h right⟩, fun ⟨hl, hr⟩ ↦ fun | left => hl | right => hr⟩

@[simp]
protected lemma «exists» {p : Player → Prop} :
    (∃ x, p x) ↔ p left ∨ p right :=
  ⟨fun | ⟨left, h⟩ => .inl h | ⟨right, h⟩ => .inr h, fun | .inl h | .inr h => ⟨_, h⟩⟩

instance : Neg Player where
  neg := cases right left

@[simp, grind =] lemma neg_left : -left = right := rfl
@[simp, grind =] lemma neg_right : -right = left := rfl
@[simp] theorem eq_neg : ∀ {p q : Player}, p = -q ↔ p ≠ q := by decide
@[simp] theorem neg_eq : ∀ {p q : Player}, -p = q ↔ p ≠ q := by decide
theorem ne_neg : ∀ {p q : Player}, p ≠ -q ↔ p = q := by decide
theorem neg_ne : ∀ {p q : Player}, -p ≠ q ↔ p = q := by decide
theorem neg_ne_self : ∀ (p : Player), -p ≠ p := by decide
theorem self_ne_neg : ∀ (p : Player), p ≠ -p := by decide

instance : InvolutiveNeg Player where
  neg_neg := by decide

/--
The multiplication of `Player`s is used to state the lemmas about the multiplication of
combinatorial games, such as `IGame.mulOption_mem_moves_mul`.
-/
instance : Mul Player where mul
  | left, p => p
  | right, p => -p

@[simp, grind =] lemma left_mul (p : Player) : left * p = p := rfl
@[simp, grind =] lemma right_mul (p : Player) : right * p = -p := rfl
@[simp, grind =] lemma mul_left : ∀ p, p * left = p := by decide
@[simp, grind =] lemma mul_right : ∀ p, p * right = -p := by decide
@[simp, grind =] lemma mul_self : ∀ p, p * p = left := by decide

instance : HasDistribNeg Player where
  neg_mul := by decide
  mul_neg := by decide

instance : CommGroup Player where
  one := left
  inv := id
  mul_assoc := by decide
  mul_comm := by decide
  one_mul := by decide
  mul_one := by decide
  inv_mul_cancel := by decide

@[simp, grind =] lemma one_eq_left : 1 = left := rfl
@[simp, grind =] lemma inv_eq_self (p : Player) : p⁻¹ = p := rfl

end Player


