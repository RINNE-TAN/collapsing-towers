import CollapsingTowers.TwoLevelMut.SyntacticSoundness.PresvPure
import CollapsingTowers.TwoLevelMut.SyntacticSoundness.PresvMut
import CollapsingTowers.TwoLevelMut.SyntacticSoundness.PresvReflect

theorem preservation.strengthened :
  ∀ Γ σ₀ σ₁ e₀ e₁ τ φ₀ ω₀,
    step_lvl Γ.length ⟨σ₀, e₀⟩ ⟨σ₁, e₁⟩ →
    ok σ₀ →
    typing_reification σ₀ Γ e₀ τ φ₀ ω₀ →
    ok σ₁ ∧
    ∃ φ₁ ω₁,
      typing_reification σ₁ Γ e₁ τ φ₁ ω₁ ∧
      φ₁ ≤ φ₀ ∧
      ω₁ ≤ ω₀ :=
  by
  intros Γ σ₀ σ₁ e₀ e₁ τ φ₀ ω₀ Hstep Hok₀ Hτ
  cases Hstep
  case pure HM Hlc Hhead =>
    cases Hτ
    case pure Hτ =>
      have ⟨φ, ω, Hτ, Hφ, Hω⟩ := preservation.pure _ _ _ _ _ _ _ _ HM Hlc Hhead Hτ
      cases φ <;> simp at Hφ
      constructor
      . apply Hok₀
      . exists ⊥, ω; exact ⟨typing_reification.pure _ _ _ _ _ Hτ, rfl, Hω⟩
    case reify Hτ =>
      have ⟨φ, ω, Hτ, Hφ, Hω⟩ := preservation.pure _ _ _ _ _ _ _ _ HM Hlc Hhead Hτ
      constructor
      . apply Hok₀
      . exists φ, ω; exact ⟨typing_reification.reify _ _ _ _ _ _ Hτ, Hφ, Hω⟩
  case mutable HM Hlc Hmut =>
    cases Hτ
    case pure Hτ =>
      have ⟨Hok₁, ω, Hτ, Hω⟩ := preservation.mutable _ _ _ _ _ _ _ _ _ HM Hlc Hmut Hok₀ Hτ
      constructor
      . apply Hok₁
      . exists ⊥, ω; exact ⟨typing_reification.pure _ _ _ _ _ Hτ, rfl, Hω⟩
    case reify Hτ =>
      have ⟨Hok₁, ω, Hτ, Hω⟩ := preservation.mutable _ _ _ _ _ _ _ _ _ HM Hlc Hmut Hok₀ Hτ
      constructor
      . apply Hok₁
      . exists φ₀, ω; exact ⟨typing_reification.reify _ _ _ _ _ _ Hτ, by simp, Hω⟩
  case reflect P E e HP HE Hlc =>
    admit
