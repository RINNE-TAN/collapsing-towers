import Mathlib.Order.Basic

inductive Stage : Type where
  | static
  | dynamic

notation:max "𝟙" => Stage.static

notation:max "𝟚" => Stage.dynamic

inductive Effect : Type where
  | reify
  | mutation (𝕊 : Stage)

@[simp]
def erase_effect : Effect → Effect
  | .reify => .reify
  | .mutation _ => .mutation 𝟚

abbrev Effects :=
  Set Effect

@[simp]
def erase_effects (φ : Effects) : Effects := Set.image erase_effect φ \ { .reify }
