import CollapsingTowers.TwoLevelMut.SyntacticSoundness.PresvPure

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
      . exists ⊥
        exact ⟨typing_reification.pure _ _ _ _ Hτ, rfl⟩
    case reify Hτ =>
      have ⟨φ, Hτ, Hφ⟩ := preservation.pure _ _ _ _ _ _ _ HM Hlc Hhead Hτ
      constructor
      . apply Hok₀
      . exists φ
        exact ⟨typing_reification.reify _ _ _ _ _ Hτ, Hφ⟩
  case mutable HM Hlc Hmut =>
    admit
  case reflect P E e HP HE Hlc =>
    admit
