import Instar.TwoLevelMut.SyntacticSoundness.PresvPure
import Instar.TwoLevelMut.SyntacticSoundness.PresvMut
import Instar.TwoLevelMut.SyntacticSoundness.PresvReflect

theorem preservation.strengthened :
  ∀ Γ σ₀ σ₁ e₀ e₁ τ ε₀,
    step_lvl Γ.length ⟨σ₀, e₀⟩ ⟨σ₁, e₁⟩ →
    typing_reification Γ e₀ τ ε₀ →
    ∃ ε₁,
      typing_reification Γ e₁ τ ε₁ ∧
      ε₁ ≤ ε₀ :=
  by
  intros Γ σ₀ σ₁ e₀ e₁ τ ε₀ Hstep Hτ
  cases Hstep
  case pure HM Hlc Hhead =>
    cases Hτ
    case pure Hτ =>
      have ⟨ε, Hτ, Hε⟩ := preservation.pure _ _ _ _ _ _ HM Hlc Hhead Hτ
      cases ε <;> simp at Hε
      exists ⊥; constructor
      . apply typing_reification.pure _ _ _ Hτ
      . simp
    case reify Hτ =>
      have ⟨ε, Hτ, Hε⟩ := preservation.pure _ _ _ _ _ _ HM Hlc Hhead Hτ
      exists ε; constructor
      . apply typing_reification.reify _ _ _ _ Hτ
      . apply Hε
  case mutable HM Hlc Hmut =>
    exfalso
    cases Hτ
    all_goals
      next Hτ => apply preservation.mutable _ _ _ _ _ _ _ _ HM Hlc Hmut Hτ
  case reflect P E e HP HE Hlc =>
    cases HP
    case hole =>
      exists ⊥; simp
      apply preservation.reflect.head _ _ _ _ _ HE Hτ
    case consℚ HQ =>
      exists ε₀; simp
      cases Hτ
      case pure Hτ =>
        apply typing_reification.pure
        apply preservation.reflect _ _ _ _ _ _ HQ HE Hlc Hτ
      case reify Hτ =>
        apply typing_reification.reify
        apply preservation.reflect _ _ _ _ _ _ HQ HE Hlc Hτ

theorem preservation :
  ∀ σ₀ σ₁ e₀ e₁ τ ε₀,
    (⟨σ₀, e₀⟩ ⭢ ⟨σ₁, e₁⟩) →
    typing_reification ⦰ e₀ τ ε₀ →
    ∃ ε₁,
      typing_reification ⦰ e₁ τ ε₁ ∧
      ε₁ ≤ ε₀ :=
  by
  intros σ₀ σ₁ e₀ e₁ τ ε₀ Hstep
  apply preservation.strengthened
  apply Hstep

theorem preservation.stepn :
  ∀ σ₀ σ₁ e₀ e₁ τ ε₀,
    (⟨σ₀, e₀⟩ ⭢* ⟨σ₁, e₁⟩) →
    typing_reification ⦰ e₀ τ ε₀ →
    ∃ ε₁,
      typing_reification ⦰ e₁ τ ε₁ ∧
      ε₁ ≤ ε₀ :=
  by
  intro σ₀ σ₂ e₀ e₂ τ ε₀ Hstepn Hτ₀
  generalize HEq₀ : (σ₀, e₀) = st₀
  generalize HEq₁ : (σ₂, e₂) = st₂
  rw [HEq₀, HEq₁] at Hstepn
  induction Hstepn generalizing ε₀ σ₀ e₀
  case refl =>
    simp [← HEq₀] at HEq₁
    rw [HEq₁.right]
    exists ε₀
  case multi st₀ st₁ st₂ Hstep Hstepn IH =>
    rcases st₁ with ⟨σ₁, e₁⟩
    rw [← HEq₀] at Hstep
    have ⟨ε₁, Hτ₁, HLeε₁⟩ := preservation _ _ _ _ _ _ Hstep Hτ₀
    have ⟨ε₂, Hτ₂, HLeε₂⟩ := IH _ _ _ Hτ₁ rfl HEq₁
    exists ε₂
    constructor; apply Hτ₂
    apply le_trans HLeε₂ HLeε₁
