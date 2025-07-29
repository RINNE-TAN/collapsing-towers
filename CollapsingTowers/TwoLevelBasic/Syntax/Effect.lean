import Mathlib.Order.Basic

inductive Effect : Type where
  | pure
  | reify

notation:max "∅" => Effect.pure

@[simp]
def Effect.union : Effect → Effect → Effect
  | .pure, .pure => .pure
  | .reify, _ => .reify
  | _, .reify => .reify

@[simp]
instance : Union Effect where union := Effect.union

@[simp]
lemma union_pure_right : forall φ : Effect, φ ∪ ∅ = φ := by
  intro φ
  cases φ <;> rfl

@[simp]
lemma union_pure_left : forall φ : Effect, ∅ ∪ φ = φ := by
  intro φ
  cases φ <;> rfl

@[simp]
lemma union_reify_right : forall φ : Effect, φ ∪ .reify = .reify := by
  intro φ
  cases φ <;> rfl

@[simp]
lemma union_reify_left : forall φ : Effect, .reify ∪ φ = .reify := by
  intro φ
  cases φ <;> rfl

@[simp]
def le : Effect → Effect → Prop
  | .pure, _ => true
  | .reify, .reify => true
  | _, _ => false

@[simp]
instance : LE Effect where le := le

instance : Preorder Effect where
  le_refl := by intro x; cases x <;> simp
  le_trans := by intros x y z; cases x <;> cases y <;> cases z <;> simp
  lt_iff_le_not_ge := by intros x y; cases x <;> cases y <;> simp

instance : PartialOrder Effect where
  le_antisymm := by
    intros x y
    cases x <;> cases y <;> simp
    all_goals intro _ _; contradiction
