import Mathlib.Order.Basic

inductive Effect : Type where
  | pure
  | reify

notation:max "⊥" => Effect.pure

notation:max "⊤" => Effect.reify

@[simp]
def Effect.union : Effect → Effect → Effect
  | ⊥, ⊥ => ⊥
  | ⊤, _ => ⊤
  | _, ⊤ => ⊤

@[simp]
instance : Union Effect where union := Effect.union

@[simp]
lemma Effect.union_pure : forall ε : Effect, ε ∪ ⊥ = ε := by
  intro ε
  cases ε <;> rfl

@[simp]
lemma Effect.pure_union : forall ε : Effect, ⊥ ∪ ε = ε := by
  intro ε
  cases ε <;> rfl

@[simp]
lemma Effect.union_reify : forall ε : Effect, ε ∪ ⊤ = ⊤ := by
  intro ε
  cases ε <;> rfl

@[simp]
lemma Effect.reify_union : forall ε : Effect, ⊤ ∪ ε = ⊤ := by
  intro ε
  cases ε <;> rfl

@[simp]
def Effect.le : Effect → Effect → Prop
  | ⊥, _ => true
  | ⊤, ⊤ => true
  | _, _ => false

@[simp]
instance : LE Effect where le := Effect.le

@[simp]
lemma Effect.le_eq (x y : Effect) : (x ≤ y) = Effect.le x y := rfl

instance : Preorder Effect where
  le_refl := by intro x; cases x <;> simp
  le_trans := by intros x y z; cases x <;> cases y <;> cases z <;> simp
  lt_iff_le_not_ge := by intros x y; cases x <;> cases y <;> simp

instance : PartialOrder Effect where
  le_antisymm := by
    intros x y
    cases x <;> cases y <;> simp
