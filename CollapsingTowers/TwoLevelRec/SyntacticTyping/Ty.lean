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
lemma Effect.union_pure : forall φ : Effect, φ ∪ ⊥ = φ := by
  intro φ
  cases φ <;> rfl

@[simp]
lemma Effect.pure_union : forall φ : Effect, ⊥ ∪ φ = φ := by
  intro φ
  cases φ <;> rfl

@[simp]
lemma Effect.union_reify : forall φ : Effect, φ ∪ ⊤ = ⊤ := by
  intro φ
  cases φ <;> rfl

@[simp]
lemma Effect.reify_union : forall φ : Effect, ⊤ ∪ φ = ⊤ := by
  intro φ
  cases φ <;> rfl

@[simp]
def Effect.le : Effect → Effect → Prop
  | ⊥, _ => true
  | ⊤, ⊤ => true
  | _, _ => false

@[simp]
instance : LE Effect where le := Effect.le

instance : Preorder Effect where
  le_refl := by intro x; cases x <;> simp
  le_trans := by intros x y z; cases x <;> cases y <;> cases z <;> simp
  lt_iff_le_not_ge := by intros x y; cases x <;> cases y <;> simp

instance : PartialOrder Effect where
  le_antisymm := by
    intros x y
    cases x <;> cases y <;> simp
    all_goals intro _ _; contradiction

inductive Ty : Type where
  | nat
  | arrow (τ𝕒 : Ty) (τ𝕓 : Ty) (φ : Effect)
  | fragment (τ : Ty)
  | rep (τ : Ty)
