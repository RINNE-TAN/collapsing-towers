import Mathlib.Order.Basic

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

abbrev Effects :=
  Set Effect

@[simp]
def erase_effects (φ : Effects) : Effects :=
  { erase_effect β | β ∈ φ } \ { .reify }

@[simp]
def escape_effects (φ : Effects) : Effects :=
  { escape_effect β | β ∈ φ }

@[simp]
def wbt_effects (𝕊 : Stage) (φ : Effects) : Prop :=
  ∀ β ∈ φ, wbt_effect 𝕊 β
