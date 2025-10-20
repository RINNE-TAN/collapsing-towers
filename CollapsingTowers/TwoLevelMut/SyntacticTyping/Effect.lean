import Mathlib.Order.Basic
import Mathlib.Data.Set.Image

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
  | 𝟙, .init 𝟙 => true
  | 𝟙, .read 𝟙 => true
  | 𝟙, .write 𝟙 => true
  | 𝟙, _ => false
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

lemma grounded_meffect.under_erase : ∀ β, wbt_meffect 𝟚 (erase_meffect β) :=
  by
  intros β
  cases β <;> simp

lemma grounded_meffects.under_erase : ∀ ω, wbt_meffects 𝟚 (erase_meffects ω) :=
  by
  intros ω β₀ Hβ₀
  have ⟨β₁, Hβ₁, HEqβ⟩ := Hβ₀
  rw [← HEqβ]
  apply grounded_meffect.under_erase

@[simp]
lemma erase_meffects.init : ∀ 𝕊, erase_meffects { .init 𝕊 } = { .init 𝟚 } :=
  by simp

@[simp]
lemma erase_meffects.read : ∀ 𝕊, erase_meffects { .read 𝕊 } = { .read 𝟚 } :=
  by simp

@[simp]
lemma erase_meffects.write : ∀ 𝕊, erase_meffects { .write 𝕊 } = { .write 𝟚 } :=
  by simp

@[simp]
lemma erase_meffects.empty : erase_meffects ∅ = ∅ :=
  by simp

@[simp]
lemma erase_meffects.union : ∀ ω₀ ω₁, erase_meffects (ω₀ ∪ ω₁) = erase_meffects ω₀ ∪ erase_meffects ω₁ :=
  by
  intros ω₀ ω₁
  simp only [erase_meffects]
  repeat rw [← Set.image]
  rw [← Set.image_union]

@[simp]
lemma erase_meffect.cancel_escape : ∀ β, (erase_meffect ∘ escape_meffect) β = erase_meffect β :=
  by
  intros β
  cases β <;> simp

@[simp]
lemma erase_meffects.cancel_escape : ∀ ω, erase_meffects (escape_meffects ω) = erase_meffects ω :=
  by
  intros ω
  simp only [erase_meffects, escape_meffects]
  repeat rw [← Set.image]
  rw [← Set.image_comp]
  rw [funext erase_meffect.cancel_escape]

@[simp]
lemma escape_meffects.empty : escape_meffects ∅ = ∅ :=
  by simp

@[simp]
lemma escape_meffects.union : ∀ ω₀ ω₁, escape_meffects (ω₀ ∪ ω₁) = escape_meffects ω₀ ∪ escape_meffects ω₁ :=
  by
  intros ω₀ ω₁
  simp only [escape_meffects]
  repeat rw [← Set.image]
  rw [← Set.image_union]

@[simp]
lemma escape_meffects.init : ∀ 𝕊, escape_meffects { .init 𝕊 } = { .init 𝟙 } :=
  by simp

@[simp]
lemma escape_meffects.read : ∀ 𝕊, escape_meffects { .read 𝕊 } = { .read 𝟙 } :=
  by simp

@[simp]
lemma escape_meffects.write : ∀ 𝕊, escape_meffects { .write 𝕊 } = { .write 𝟙 } :=
  by simp
