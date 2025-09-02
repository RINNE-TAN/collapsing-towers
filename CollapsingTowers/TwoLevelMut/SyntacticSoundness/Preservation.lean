import CollapsingTowers.TwoLevelMut.SyntacticSoundness.PresvPure
import CollapsingTowers.TwoLevelMut.SyntacticSoundness.PresvMut
import CollapsingTowers.TwoLevelMut.SyntacticSoundness.PresvReflect

theorem preservation.strengthened :
  ∀ Γ σ₀ σ₁ e₀ e₁ τ φ₀,
    step_lvl Γ.length ⟨σ₀, e₀⟩ ⟨σ₁, e₁⟩ →
    ok σ₀ →
    typing_reification σ₀ Γ e₀ τ φ₀ →
    ok σ₁ ∧
    ∃ φ₁,
      typing_reification σ₁ Γ e₁ τ φ₁ ∧
      φ₁ ≤ φ₀ :=
  by
  intros Γ σ₀ σ₁ e₀ e₁ τ φ₀ Hstep Hok₀ Hτ
  cases Hstep
  case pure HM Hlc Hhead =>
    cases Hτ
    case pure Hτ =>
      have ⟨φ, Hτ, Hφ⟩ := preservation.pure _ _ _ _ _ _ _ HM Hlc Hhead Hτ
      cases φ <;> simp at Hφ
      constructor
      . apply Hok₀
      . exists ⊥; exact ⟨typing_reification.pure _ _ _ _ Hτ, rfl⟩
    case reify Hτ =>
      have ⟨φ, Hτ, Hφ⟩ := preservation.pure _ _ _ _ _ _ _ HM Hlc Hhead Hτ
      constructor
      . apply Hok₀
      . exists φ; exact ⟨typing_reification.reify _ _ _ _ _ Hτ, Hφ⟩
  case mutable HM Hlc Hmut =>
    cases Hτ
    case pure Hτ =>
      have ⟨Hok₁, Hτ⟩ := preservation.mutable _ _ _ _ _ _ _ _ HM Hlc Hmut Hok₀ Hτ
      constructor
      . apply Hok₁
      . exists ⊥; exact ⟨typing_reification.pure _ _ _ _ Hτ, rfl⟩
    case reify Hτ =>
      have ⟨Hok₁, Hτ⟩ := preservation.mutable _ _ _ _ _ _ _ _ HM Hlc Hmut Hok₀ Hτ
      constructor
      . apply Hok₁
      . exists φ₀; exact ⟨typing_reification.reify _ _ _ _ _ Hτ, (by simp)⟩
  case reflect P E e HP HE Hlc =>
    cases HP
    case hole =>
      have Hτ := preservation.reflect.head _ _ _ _ _ _ HE Hτ
      constructor
      . apply Hok₀
      . exists ⊥
    case consℚ HQ =>
      cases Hτ
      case pure Hτ =>
        have Hτ := preservation.reflect _ _ _ _ _ _ _ HQ HE Hlc Hτ
        constructor
        . apply Hok₀
        . exists ⊥; exact ⟨typing_reification.pure _ _ _ _ Hτ, rfl⟩
      case reify Hτ =>
        have Hτ := preservation.reflect _ _ _ _ _ _ _ HQ HE Hlc Hτ
        constructor
        . apply Hok₀
        . exists φ₀; exact ⟨typing_reification.reify _ _ _ _ _ Hτ, (by simp)⟩

theorem preservation :
  ∀ σ₀ σ₁ e₀ e₁ τ φ₀,
    (⟨σ₀, e₀⟩ ⇝ ⟨σ₁, e₁⟩) →
    ok σ₀ →
    typing_reification σ₀ ⦰ e₀ τ φ₀ →
    ok σ₁ ∧
    ∃ φ₁,
      typing_reification σ₁ ⦰ e₁ τ φ₁ ∧
      φ₁ ≤ φ₀ :=
  by
  intros σ₀ σ₁ e₀ e₁ τ φ₀ Hstep
  apply preservation.strengthened
  apply Hstep

theorem preservation.stepn :
  ∀ σ₀ σ₁ e₀ e₁ τ φ₀,
    (⟨σ₀, e₀⟩ ⇝* ⟨σ₁, e₁⟩) →
    ok σ₀ →
    typing_reification σ₀ ⦰ e₀ τ φ₀ →
    ok σ₁ ∧
    ∃ φ₁,
      typing_reification σ₁ ⦰ e₁ τ φ₁ ∧
      φ₁ ≤ φ₀ :=
  by
  intro σ₀ σ₂ e₀ e₂ τ φ₀ Hstepn Hok₀ Hτ₀
  generalize HEq₀ : (σ₀, e₀) = st₀
  generalize HEq₁ : (σ₂, e₂) = st₂
  rw [HEq₀, HEq₁] at Hstepn
  induction Hstepn generalizing φ₀ σ₀ e₀
  case refl =>
    simp [← HEq₀] at HEq₁
    rw [HEq₁.left, HEq₁.right]
    constructor; apply Hok₀
    exists φ₀
  case multi st₀ st₁ st₂ Hstep Hstepn IH =>
    rcases st₁ with ⟨σ₁, e₁⟩
    rw [← HEq₀] at Hstep
    have ⟨Hok₁, φ₁, Hτ₁, HLeφ₁⟩ := preservation _ _ _ _ _ _ Hstep Hok₀ Hτ₀
    have ⟨Hok₂, φ₂, Hτ₂, HLeφ₂⟩ := IH _ _ _ Hok₁ Hτ₁ rfl HEq₁
    constructor; apply Hok₂
    exists φ₂
    constructor; apply Hτ₂
    apply le_trans HLeφ₂ HLeφ₁
