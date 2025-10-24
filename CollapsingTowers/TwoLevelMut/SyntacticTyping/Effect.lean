import Mathlib.Data.Set.Image

-- mutation effect
inductive Stage : Type where
  | static
  | dynamic

notation:max "𝟙" => Stage.static

notation:max "𝟚" => Stage.dynamic

inductive Effect : Type where
  | init (𝕊 : Stage)
  | read (𝕊 : Stage)
  | write (𝕊 : Stage)

abbrev Effects :=
  Set Effect

@[simp]
def stage_effect : Stage → Effect → Prop
  | 𝟙, .init 𝟙 => true
  | 𝟙, .read 𝟙 => true
  | 𝟙, .write 𝟙 => true
  | 𝟙, _ => false
  | 𝟚, .init 𝟚 => true
  | 𝟚, .read 𝟚 => true
  | 𝟚, .write 𝟚 => true
  | 𝟚, _ => false

@[simp]
def stage_effects (𝕊 : Stage) (ω : Effects) : Prop :=
  ∀ β ∈ ω, stage_effect 𝕊 β

-- erase
@[simp]
def erase_effect : Effect → Effect
  | .init _ => .init 𝟚
  | .read _ => .read 𝟚
  | .write _ => .write 𝟚

@[simp]
def erase_effects (ω : Effects) : Effects :=
  { erase_effect β | β ∈ ω }

-- escape
@[simp]
def escape_effect : Effect → Effect
  | .init _ => .init 𝟙
  | .read _ => .read 𝟙
  | .write _ => .write 𝟙

@[simp]
def escape_effects (ω : Effects) : Effects :=
  { escape_effect β | β ∈ ω }

-- stage lemma
lemma stage_effect.under_erase : ∀ β, stage_effect 𝟚 (erase_effect β) :=
  by
  intros β
  cases β <;> simp

lemma stage_effects.under_erase : ∀ ω, stage_effects 𝟚 (erase_effects ω) :=
  by
  intros ω β₀ Hβ₀
  have ⟨β₁, Hβ₁, HEqβ⟩ := Hβ₀
  rw [← HEqβ]
  apply stage_effect.under_erase

lemma stage_effect.under_escape : ∀ β, stage_effect 𝟙 (escape_effect β) :=
  by
  intros β
  cases β <;> simp

lemma stage_effects.under_escape : ∀ ω, stage_effects 𝟙 (escape_effects ω) :=
  by
  intros ω β₀ Hβ₀
  have ⟨β₁, Hβ₁, HEqβ⟩ := Hβ₀
  rw [← HEqβ]
  apply stage_effect.under_escape

lemma stage_effects.mono : ∀ 𝕊 ω₀ ω₁, ω₁ ≤ ω₀ → stage_effects 𝕊 ω₀ → stage_effects 𝕊 ω₁ :=
  by
  intros 𝕊 ω₀ ω₁ HLeω Hω β₀ Hβ₀
  apply Hω _ (Set.mem_of_subset_of_mem HLeω Hβ₀)

lemma stage_effects.disjoint : ∀ ω, stage_effects 𝟙 ω → stage_effects 𝟚 ω → ω = ∅ :=
  by
  intros ω Hω₁ Hω₂
  apply Set.eq_empty_of_forall_notMem
  intros β Hβ
  have H₁ := Hω₁ _ Hβ
  have H₂ := Hω₂ _ Hβ
  cases β
  all_goals next 𝕊 =>
    cases 𝕊 <;> simp at H₁ H₂

lemma stage_effects.diff :
  ∀ 𝕊 ω₀ ω₁,
    stage_effects 𝕊 ω₀ →
    stage_effects 𝕊 ω₁ →
    stage_effects 𝕊 (ω₀ \ ω₁) :=
  by
  intros 𝕊 ω₀ ω₁ Hω₀ Hω₁
  intros β Hβ
  apply Hω₀
  apply Set.mem_of_subset_of_mem _ Hβ
  apply Set.diff_subset

lemma stage_effects.union :
  ∀ 𝕊 ω₀ ω₁,
    stage_effects 𝕊 ω₀ →
    stage_effects 𝕊 ω₁ →
    stage_effects 𝕊 (ω₀ ∪ ω₁) :=
  by
  intros 𝕊 ω₀ ω₁ Hω₀ Hω₁
  intros β Hβ
  cases Hβ
  case inl Hβ₀ => apply Hω₀ _ Hβ₀
  case inr Hβ₁ => apply Hω₁ _ Hβ₁

-- erase lemma
@[simp]
lemma erase_effects.init : ∀ 𝕊, erase_effects { .init 𝕊 } = { .init 𝟚 } :=
  by simp

@[simp]
lemma erase_effects.read : ∀ 𝕊, erase_effects { .read 𝕊 } = { .read 𝟚 } :=
  by simp

@[simp]
lemma erase_effects.write : ∀ 𝕊, erase_effects { .write 𝕊 } = { .write 𝟚 } :=
  by simp

@[simp]
lemma erase_effects.empty : erase_effects ∅ = ∅ :=
  by simp

@[simp]
lemma erase_effects.union : ∀ ω₀ ω₁, erase_effects (ω₀ ∪ ω₁) = erase_effects ω₀ ∪ erase_effects ω₁ :=
  by
  intros ω₀ ω₁
  simp only [erase_effects]
  repeat rw [← Set.image]
  rw [← Set.image_union]

@[simp]
lemma erase_effect.cancel_escape : ∀ β, (erase_effect ∘ escape_effect) β = erase_effect β :=
  by
  intros β
  cases β <;> simp

@[simp]
lemma erase_effects.cancel_escape : ∀ ω, erase_effects (escape_effects ω) = erase_effects ω :=
  by
  intros ω
  simp only [erase_effects, escape_effects]
  repeat rw [← Set.image]
  rw [← Set.image_comp]
  rw [funext erase_effect.cancel_escape]

-- escape lemma
@[simp]
lemma escape_effects.empty : escape_effects ∅ = ∅ :=
  by simp

@[simp]
lemma escape_effects.union : ∀ ω₀ ω₁, escape_effects (ω₀ ∪ ω₁) = escape_effects ω₀ ∪ escape_effects ω₁ :=
  by
  intros ω₀ ω₁
  simp only [escape_effects]
  repeat rw [← Set.image]
  rw [← Set.image_union]

@[simp]
lemma escape_effects.init : ∀ 𝕊, escape_effects { .init 𝕊 } = { .init 𝟙 } :=
  by simp

@[simp]
lemma escape_effects.read : ∀ 𝕊, escape_effects { .read 𝕊 } = { .read 𝟙 } :=
  by simp

@[simp]
lemma escape_effects.write : ∀ 𝕊, escape_effects { .write 𝕊 } = { .write 𝟙 } :=
  by simp

lemma escape_effects.mono : ∀ ω₀ ω₁, ω₀ ≤ ω₁ → escape_effects ω₀ ≤ escape_effects ω₁ :=
  by
  intros ω₀ ω₁ HLeω
  intros β₀ Hβ₀
  have ⟨β₁, Hβ₁, HEqβ⟩ := Hβ₀
  exists β₁
  constructor
  . apply HLeω Hβ₁
  . apply HEqβ
