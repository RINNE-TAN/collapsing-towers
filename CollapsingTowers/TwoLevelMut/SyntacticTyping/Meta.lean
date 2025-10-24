import Mathlib.Order.Basic

inductive Meta : Type where
  | pure
  | reify

notation:max "⊥" => Meta.pure

notation:max "⊤" => Meta.reify

@[simp]
def Meta.union : Meta → Meta → Meta
  | ⊥, ⊥ => ⊥
  | ⊤, _ => ⊤
  | _, ⊤ => ⊤

@[simp]
instance : Union Meta where union := Meta.union

@[simp]
lemma Meta.union_pure : forall φ : Meta, φ ∪ ⊥ = φ := by
  intro φ
  cases φ <;> rfl

@[simp]
lemma Meta.pure_union : forall φ : Meta, ⊥ ∪ φ = φ := by
  intro φ
  cases φ <;> rfl

@[simp]
lemma Meta.union_reify : forall φ : Meta, φ ∪ ⊤ = ⊤ := by
  intro φ
  cases φ <;> rfl

@[simp]
lemma Meta.reify_union : forall φ : Meta, ⊤ ∪ φ = ⊤ := by
  intro φ
  cases φ <;> rfl

@[simp]
def Meta.le : Meta → Meta → Prop
  | ⊥, _ => true
  | ⊤, ⊤ => true
  | _, _ => false

@[simp]
instance : LE Meta where le := Meta.le

instance : Preorder Meta where
  le_refl := by intro x; cases x <;> simp
  le_trans := by intros x y z; cases x <;> cases y <;> cases z <;> simp
  lt_iff_le_not_ge := by intros x y; cases x <;> cases y <;> simp

instance : PartialOrder Meta where
  le_antisymm := by
    intros x y
    cases x <;> cases y <;> simp
    all_goals intro _ _; contradiction
