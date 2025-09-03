import Mathlib.Data.Nat.Basic

@[simp]
def bijection {α β} (r : α → β → Prop): Prop :=
  (∀ x y z, r x y → r x z → y = z) ∧
  (∀ x y z, r x z → r y z → x = y)

abbrev World :=
  ℕ → ℕ → Prop

@[simp]
def World.future (𝓦₀ 𝓦₁ : World) : Prop :=
  ∀ x y, 𝓦₁ x y → 𝓦₀ x y

notation:max 𝓦₁ " ⊒ " 𝓦₀  => World.future 𝓦₀ 𝓦₁

@[simp]
def World.empty : World :=
  fun _ _ => false

@[simp]
def World.ext (𝓦 : World) (l₀ l₁ : ℕ) : World :=
  fun x y => (x = l₀ ∧ y = l₁) ∨ 𝓦 l₀ l₁
