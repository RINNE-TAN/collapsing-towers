import Mathlib.Order.Basic
import Mathlib.Data.Set.Image

inductive Stage : Type where
  | static
  | dynamic

notation:max "𝟙" => Stage.static

notation:max "𝟚" => Stage.dynamic

inductive Effect : Type where
  | reify
  | mutate (𝕊 : Stage)

@[simp]
def erase_effect : Effect → Effect
  | .reify => .reify
  | .mutate _ => .mutate 𝟚

@[simp]
def escape_effect : Effect → Effect
  | .reify => .reify
  | .mutate _ => .mutate 𝟙

@[simp]
def wbt_effect : Stage → Effect → Prop
  | 𝟙, _ => true
  | 𝟚, (.mutate 𝟚) => true
  | 𝟚, _ => false

lemma grounded_effect.under_erase : ∀ β, β ≠ .reify → wbt_effect 𝟚 (erase_effect β) :=
  by intros β; cases β <;> simp

abbrev Effects :=
  Set Effect

@[simp]
def erase_effects (φ : Effects) : Effects :=
  { erase_effect β | β ∈ φ \ { .reify } }

@[simp]
def escape_effects (φ : Effects) : Effects :=
  { escape_effect β | β ∈ φ }

@[simp]
def wbt_effects (𝕊 : Stage) (φ : Effects) : Prop :=
  ∀ β ∈ φ, wbt_effect 𝕊 β

lemma grounded_effects.under_erase : ∀ φ, wbt_effects 𝟚 (erase_effects φ) :=
  by
  intros φ β₀ Hβ₀
  have ⟨β₁, Hβ₁, HEqβ⟩ := Hβ₀
  rw [← HEqβ]; apply grounded_effect.under_erase
  apply Hβ₁.right

@[simp]
def erase_effects.union : ∀ φ₀ φ₁, erase_effects (φ₀ ∪ φ₁) = erase_effects φ₀ ∪ erase_effects φ₁ :=
  by
  intros φ₀ φ₁
  simp only [erase_effects]
  repeat rw [← Set.image]
  rw [← Set.image_union, Set.union_diff_distrib]

@[simp]
def erase_effects.reify : erase_effects { .reify } = ∅ :=
  by simp

@[simp]
lemma erase_effects.mutate : ∀ 𝕊, erase_effects { .mutate 𝕊 } = { .mutate 𝟚 } :=
  by simp

@[simp]
def erase_effects.diff_reify : ∀ φ, erase_effects (φ \ { .reify }) = erase_effects φ :=
  by simp

@[simp]
def wbt_effects.union : ∀ 𝕊 φ₀ φ₁, wbt_effects 𝕊 (φ₀ ∪ φ₁) ↔ (wbt_effects 𝕊 φ₀ ∧ wbt_effects 𝕊 φ₁) :=
  by
  intros 𝕊 φ₀ φ₁
  constructor
  . intros Hφ
    constructor
    . intros β Hβ
      apply Hφ
      apply Set.mem_union_left _ Hβ
    . intros β Hβ
      apply Hφ
      apply Set.mem_union_right _ Hβ
  . intros Hφ
    intros β Hβ
    cases Hβ
    case inl Hβ => apply Hφ.left _ Hβ
    case inr Hβ => apply Hφ.right _ Hβ
