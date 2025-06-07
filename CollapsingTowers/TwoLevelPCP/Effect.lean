
import Mathlib.Order.Basic
inductive Effects : Type where
  | pure
  | reflect

@[simp]
def union : Effects → Effects → Effects
  | .pure, .pure => .pure
  | .reflect, _ => .reflect
  | _, .reflect => .reflect

@[simp]
def le : Effects → Effects → Prop
  | .pure, _ => true
  | .reflect, .reflect => true
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
  lt_iff_le_not_le := by intros x y; cases x <;> cases y <;> simp

instance : PartialOrder Effects where
  le_antisymm := by
    intros x y
    cases x <;> cases y <;> simp
    all_goals intro _ _; contradiction

theorem union_empty : forall φ : Effects, φ ∪ ∅ = φ := by
  intro φ
  cases φ <;> rfl
