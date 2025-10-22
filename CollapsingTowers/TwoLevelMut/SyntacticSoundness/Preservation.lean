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
      have ⟨φ, ω, Hτ, Hφ, Hω, _⟩ := preservation.pure _ _ _ _ _ _ _ _ HM Hlc Hhead Hτ
      cases φ <;> simp at Hφ
      constructor
      . apply Hok₀
      . exists ⊥, ω; exact ⟨typing_reification.pure _ _ _ _ _ Hτ, rfl, Hω⟩
    case reify Hτ =>
      have ⟨φ, ω, Hτ, Hφ, Hω, _⟩ := preservation.pure _ _ _ _ _ _ _ _ HM Hlc Hhead Hτ
      constructor
      . apply Hok₀
      . exists φ, ω; exact ⟨typing_reification.reify _ _ _ _ _ _ Hτ, Hφ, Hω⟩
  case mutable HM Hlc Hmut =>
    cases Hτ
    case pure Hτ =>
      have ⟨Hok₁, ω, Hτ, Hω, _⟩ := preservation.mutable _ _ _ _ _ _ _ _ _ HM Hlc Hmut Hok₀ Hτ
      constructor
      . apply Hok₁
      . exists ⊥, ω; exact ⟨typing_reification.pure _ _ _ _ _ Hτ, rfl, Hω⟩
    case reify Hτ =>
      have ⟨Hok₁, ω, Hτ, Hω, _⟩ := preservation.mutable _ _ _ _ _ _ _ _ _ HM Hlc Hmut Hok₀ Hτ
      constructor
      . apply Hok₁
      . exists φ₀, ω; exact ⟨typing_reification.reify _ _ _ _ _ _ Hτ, by simp, Hω⟩
  case reflect P E e HP HE Hlc =>
    admit

theorem preservation :
  ∀ σ₀ σ₁ e₀ e₁ τ φ₀ ω₀,
    (⟨σ₀, e₀⟩ ⇝ ⟨σ₁, e₁⟩) →
    ok σ₀ →
    typing_reification σ₀ ⦰ e₀ τ φ₀ ω₀ →
    ok σ₁ ∧
    ∃ φ₁ ω₁,
      typing_reification σ₁ ⦰ e₁ τ φ₁ ω₁ ∧
      φ₁ ≤ φ₀ ∧
      ω₁ ≤ ω₀ :=
  by
  intros σ₀ σ₁ e₀ e₁ τ φ₀ ω₀ Hstep
  apply preservation.strengthened
  apply Hstep

theorem preservation.stepn :
  ∀ σ₀ σ₁ e₀ e₁ τ φ₀ ω₀,
    (⟨σ₀, e₀⟩ ⇝* ⟨σ₁, e₁⟩) →
    ok σ₀ →
    typing_reification σ₀ ⦰ e₀ τ φ₀ ω₀ →
    ok σ₁ ∧
    ∃ φ₁ ω₁,
      typing_reification σ₁ ⦰ e₁ τ φ₁ ω₁ ∧
      φ₁ ≤ φ₀ ∧
      ω₁ ≤ ω₀ :=
  by
  intro σ₀ σ₂ e₀ e₂ τ φ₀ ω₀ Hstepn Hok₀ Hτ₀
  generalize HEq₀ : (σ₀, e₀) = st₀
  generalize HEq₁ : (σ₂, e₂) = st₂
  rw [HEq₀, HEq₁] at Hstepn
  induction Hstepn generalizing φ₀ ω₀ σ₀ e₀
  case refl =>
    simp [← HEq₀] at HEq₁
    rw [HEq₁.left, HEq₁.right]
    constructor; apply Hok₀
    exists φ₀, ω₀
  case multi st₀ st₁ st₂ Hstep Hstepn IH =>
    rcases st₁ with ⟨σ₁, e₁⟩
    rw [← HEq₀] at Hstep
    have ⟨Hok₁, φ₁, ω₁, Hτ₁, HLeφ₁, HLeω₁⟩ := preservation _ _ _ _ _ _ _ Hstep Hok₀ Hτ₀
    have ⟨Hok₂, φ₂, ω₂, Hτ₂, HLeφ₂, HLeω₂⟩ := IH _ _ _ _ Hok₁ Hτ₁ rfl HEq₁
    constructor; apply Hok₂
    exists φ₂, ω₂
    constructor; apply Hτ₂
    constructor
    . apply le_trans HLeφ₂ HLeφ₁
    . apply le_trans HLeω₂ HLeω₁
