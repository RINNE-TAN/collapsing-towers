
import Mathlib.Order.Basic
inductive Effects : Type where
  | pure
  | reify

@[simp]
def union : Effects → Effects → Effects
  | .pure, .pure => .pure
  | .reify, _ => .reify
  | _, .reify => .reify

@[simp]
def le : Effects → Effects → Prop
  | .pure, _ => true
  | .reify, .reify => true
  | _, _ => false

@[simp]
instance : EmptyCollection Effects where emptyCollection := .pure

@[simp]
instance : Union Effects where union := union

@[simp]
instance : LE Effects where le := le

instance : Preorder Effects where
  le_refl := by intro x; cases x <;> simp
  le_trans := by intros x y z; cases x <;> cases y <;> cases z <;> simp
  lt_iff_le_not_ge := by intros x y; cases x <;> cases y <;> simp

instance : PartialOrder Effects where
  le_antisymm := by
    intros x y
    cases x <;> cases y <;> simp
    all_goals intro _ _; contradiction

theorem union_pure_right : forall φ : Effects, φ ∪ ∅ = φ := by
  intro φ
  cases φ <;> rfl

theorem union_pure_left : forall φ : Effects, ∅ ∪ φ = φ := by
  intro φ
  cases φ <;> rfl

theorem union_reify_right : forall φ : Effects, φ ∪ .reify = .reify := by
  intro φ
  cases φ <;> rfl

theorem union_reify_left : forall φ : Effects, .reify ∪ φ = .reify := by
  intro φ
  cases φ <;> rfl
