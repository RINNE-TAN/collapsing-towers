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
def stage_meffect : Stage → MEffect → Prop
  | 𝟙, .init 𝟙 => true
  | 𝟙, .read 𝟙 => true
  | 𝟙, .write 𝟙 => true
  | 𝟙, _ => false
  | 𝟚, .init 𝟚 => true
  | 𝟚, .read 𝟚 => true
  | 𝟚, .write 𝟚 => true
  | 𝟚, _ => false

@[simp]
def stage_meffects (𝕊 : Stage) (ω : MEffects) : Prop :=
  ∀ β ∈ ω, stage_meffect 𝕊 β

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

-- stage lemma
lemma stage_meffect.under_erase : ∀ β, stage_meffect 𝟚 (erase_meffect β) :=
  by
  intros β
  cases β <;> simp

lemma stage_meffects.under_erase : ∀ ω, stage_meffects 𝟚 (erase_meffects ω) :=
  by
  intros ω β₀ Hβ₀
  have ⟨β₁, Hβ₁, HEqβ⟩ := Hβ₀
  rw [← HEqβ]
  apply stage_meffect.under_erase

lemma stage_meffect.under_escape : ∀ β, stage_meffect 𝟙 (escape_meffect β) :=
  by
  intros β
  cases β <;> simp

lemma stage_meffects.under_escape : ∀ ω, stage_meffects 𝟙 (escape_meffects ω) :=
  by
  intros ω β₀ Hβ₀
  have ⟨β₁, Hβ₁, HEqβ⟩ := Hβ₀
  rw [← HEqβ]
  apply stage_meffect.under_escape

lemma stage_meffects.mono : ∀ 𝕊 ω₀ ω₁, ω₁ ≤ ω₀ → stage_meffects 𝕊 ω₀ → stage_meffects 𝕊 ω₁ :=
  by
  intros 𝕊 ω₀ ω₁ HLeω Hω β₀ Hβ₀
  apply Hω _ (Set.mem_of_subset_of_mem HLeω Hβ₀)

lemma stage_meffects.disjoint : ∀ ω, stage_meffects 𝟙 ω → stage_meffects 𝟚 ω → ω = ∅ :=
  by
  intros ω Hω₁ Hω₂
  apply Set.eq_empty_of_forall_notMem
  intros β Hβ
  have H₁ := Hω₁ _ Hβ
  have H₂ := Hω₂ _ Hβ
  cases β
  all_goals next 𝕊 =>
    cases 𝕊 <;> simp at H₁ H₂

lemma stage_meffects.diff :
  ∀ 𝕊 ω₀ ω₁,
    stage_meffects 𝕊 ω₀ →
    stage_meffects 𝕊 ω₁ →
    stage_meffects 𝕊 (ω₀ \ ω₁) :=
  by
  intros 𝕊 ω₀ ω₁ Hω₀ Hω₁
  intros β Hβ
  apply Hω₀
  apply Set.mem_of_subset_of_mem _ Hβ
  apply Set.diff_subset

lemma stage_meffects.union :
  ∀ 𝕊 ω₀ ω₁,
    stage_meffects 𝕊 ω₀ →
    stage_meffects 𝕊 ω₁ →
    stage_meffects 𝕊 (ω₀ ∪ ω₁) :=
  by
  intros 𝕊 ω₀ ω₁ Hω₀ Hω₁
  intros β Hβ
  cases Hβ
  case inl Hβ₀ => apply Hω₀ _ Hβ₀
  case inr Hβ₁ => apply Hω₁ _ Hβ₁

-- erase lemma
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

-- escape lemma
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

lemma escape_meffects.mono : ∀ ω₀ ω₁, ω₀ ≤ ω₁ → escape_meffects ω₀ ≤ escape_meffects ω₁ :=
  by
  intros ω₀ ω₁ HLeω
  intros β₀ Hβ₀
  have ⟨β₁, Hβ₁, HEqβ⟩ := Hβ₀
  exists β₁
  constructor
  . apply HLeω Hβ₁
  . apply HEqβ
