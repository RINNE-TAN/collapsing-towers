import Mathlib.Order.Basic

-- reification effect
inductive REffects : Type where
  | pure
  | reify

notation:max "⊥" => REffects.pure

notation:max "⊤" => REffects.reify

@[simp]
def REffects.union : REffects → REffects → REffects
  | ⊥, ⊥ => ⊥
  | ⊤, _ => ⊤
  | _, ⊤ => ⊤

@[simp]
instance : Union REffects where union := REffects.union

@[simp]
lemma REffects.union_pure : forall φ : REffects, φ ∪ ⊥ = φ := by
  intro φ
  cases φ <;> rfl

@[simp]
lemma REffects.pure_union : forall φ : REffects, ⊥ ∪ φ = φ := by
  intro φ
  cases φ <;> rfl

@[simp]
lemma REffects.union_reify : forall φ : REffects, φ ∪ ⊤ = ⊤ := by
  intro φ
  cases φ <;> rfl

@[simp]
lemma REffects.reify_union : forall φ : REffects, ⊤ ∪ φ = ⊤ := by
  intro φ
  cases φ <;> rfl

@[simp]
def REffects.le : REffects → REffects → Prop
  | ⊥, _ => true
  | ⊤, ⊤ => true
  | _, _ => false

@[simp]
instance : LE REffects where le := REffects.le

instance : Preorder REffects where
  le_refl := by intro x; cases x <;> simp
  le_trans := by intros x y z; cases x <;> cases y <;> cases z <;> simp
  lt_iff_le_not_ge := by intros x y; cases x <;> cases y <;> simp

instance : PartialOrder REffects where
  le_antisymm := by
    intros x y
    cases x <;> cases y <;> simp
    all_goals intro _ _; contradiction

-- mutation effect
inductive Stage : Type where
  | static
  | dynamic

notation:max "𝟙" => Stage.static

notation:max "𝟚" => Stage.dynamic

inductive MEffect : Type where
  | init (𝕊 : Stage)
  | read (𝕊 : Stage)
  | write (𝕊 : Stage)

abbrev MEffects :=
  Set MEffect

-- wbt
@[simp]
def wbt_meffect : Stage → MEffect → Prop
  | 𝟙, _ => true
  | 𝟚, .init 𝟚 => true
  | 𝟚, .read 𝟚 => true
  | 𝟚, .write 𝟚 => true
  | 𝟚, _ => false

@[simp]
def wbt_meffects (𝕊 : Stage) (ω : MEffects) : Prop :=
  ∀ β ∈ ω, wbt_meffect 𝕊 β

-- erase
@[simp]
def erase_meffect : MEffect → MEffect
  | .init _ => .init 𝟚
  | .read _ => .read 𝟚
  | .write _ => .write 𝟚

@[simp]
def erase_meffects (ω : MEffects) : MEffects :=
  { erase_meffect β | β ∈ ω }

-- escape
@[simp]
def escape_meffect : MEffect → MEffect
  | .init _ => .init 𝟙
  | .read _ => .read 𝟙
  | .write _ => .write 𝟙

@[simp]
def escape_meffects (ω : MEffects) : MEffects :=
  { escape_meffect β | β ∈ ω }
