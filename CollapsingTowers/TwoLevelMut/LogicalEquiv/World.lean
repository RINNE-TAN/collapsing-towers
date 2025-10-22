import Mathlib.Data.Nat.Basic

abbrev World :=
  ℕ → ℕ → Prop

@[simp]
def World.dom (𝓦 : World) : Set ℕ := {x | ∃ y, 𝓦 x y}

@[simp]
def World.range (𝓦 : World) : Set ℕ := {y | ∃ x, 𝓦 x y}

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

@[simp]
def PartialBijection {α β} (r : α → β → Prop): Prop :=
  (∀ x y z, r x y → r x z → y = z) ∧
  (∀ x y z, r x z → r y z → x = y)

lemma PartialBijection.ext :
  ∀ 𝓦 l₀ l₁,
    PartialBijection 𝓦 →
    l₀ ∉ World.dom 𝓦 →
    l₁ ∉ World.range 𝓦 →
    PartialBijection (World.ext 𝓦 l₀ l₁) :=
  by
  intros 𝓦 l₀ l₁ Hpb Hdom Hrange
  constructor
  . intros x y z Hrel₀ Hrel₁
    match Hrel₀, Hrel₁ with
    | .inl HEq₀, .inl HEq₁ =>
      omega
    | .inl HEq₀, .inr Hrel₁ =>
      exfalso; apply Hdom
      rw [HEq₀.left] at Hrel₁
      constructor; apply Hrel₁
    | .inr Hrel₀, .inl HEq₁ =>
      exfalso; apply Hdom
      rw [HEq₁.left] at Hrel₀
      constructor; apply Hrel₀
    | .inr Hrel₀, .inr Hrel₁ =>
      apply Hpb.left
      apply Hrel₀; apply Hrel₁
  . intros x y z Hrel₀ Hrel₁
    match Hrel₀, Hrel₁ with
    | .inl HEq₀, .inl HEq₁ =>
      omega
    | .inl HEq₀, .inr Hrel₁ =>
      exfalso; apply Hrange
      rw [HEq₀.right] at Hrel₁
      constructor; apply Hrel₁
    | .inr Hrel₀, .inl HEq₁ =>
      exfalso; apply Hrange
      rw [HEq₁.right] at Hrel₀
      constructor; apply Hrel₀
    | .inr Hrel₀, .inr Hrel₁ =>
      apply Hpb.right
      apply Hrel₀; apply Hrel₁

lemma PartialBijection.eq_or_disjoint :
  ∀ (𝓦 : World) x y a b,
    PartialBijection 𝓦 →
    𝓦 x y →
    𝓦 a b →
    (x = a ∧ y = b) ∨
    (x ≠ a ∧ y ≠ b):=
  by
  intros 𝓦 x y a b Hpb Hrel₀ Hrel₁
  by_cases HEqx : x = a
  . simp [HEqx]
    simp [← HEqx] at Hrel₁
    apply Hpb.left _ _ _ Hrel₀ Hrel₁
  . simp [HEqx]
    by_cases HEqy : y = b
    . simp [HEqy]
      apply HEqx
      simp [← HEqy] at Hrel₁
      apply Hpb.right _ _ _ Hrel₀ Hrel₁
    . simp [HEqy]
