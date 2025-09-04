import Mathlib.Data.Nat.Basic

@[simp]
def bijection {α β} (r : α → β → Prop): Prop :=
  (∀ x y z, r x y → r x z → y = z) ∧
  (∀ x y z, r x z → r y z → x = y)

abbrev World :=
  ℕ → ℕ → Prop

@[simp]
def World.empty : World :=
  fun _ _ => false

@[simp]
def World.ext (𝓦 : World) (l₀ l₁ : ℕ) : World :=
  fun x y => (x = l₀ ∧ y = l₁) ∨ 𝓦 x y

@[simp]
def World.future (𝓦₀ 𝓦₁ : World) : Prop :=
  ∀ x y, 𝓦₀ x y → 𝓦₁ x y

notation:max 𝓦₁ " ⊒ " 𝓦₀  => World.future 𝓦₀ 𝓦₁

@[simp]
lemma World.future.refl : ∀ 𝓦, 𝓦 ⊒ 𝓦 := by simp

@[simp]
lemma World.future.ext : ∀ 𝓦 l₀ l₁, (World.ext 𝓦 l₀ l₁) ⊒ 𝓦 :=
  by
  intros 𝓦 l₀ l₁ x y Hrel
  right; apply Hrel

@[simp]
lemma World.future.trans :
  ∀ 𝓦₀ 𝓦₁ 𝓦₂,
    (𝓦₂ ⊒ 𝓦₁) →
    (𝓦₁ ⊒ 𝓦₀) →
    (𝓦₂ ⊒ 𝓦₀) :=
  by
  intros 𝓦₀ 𝓦₁ 𝓦₂ Hfuture₁ Hfuture₀ x y Hrel₀
  apply Hfuture₁; apply Hfuture₀
  apply Hrel₀
