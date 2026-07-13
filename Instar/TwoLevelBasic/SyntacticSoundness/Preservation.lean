import Instar.TwoLevelBasic.SyntacticSoundness.PresvPure
import Instar.TwoLevelBasic.SyntacticSoundness.PresvReflect

theorem preservation.strengthened :
  ∀ Γ e₀ e₁ τ ε₀,
    step_lvl Γ.length e₀ e₁ →
    typing_reification Γ e₀ τ ε₀ →
    ∃ ε₁,
      typing_reification Γ e₁ τ ε₁ ∧
      ε₁ ≤ ε₀ :=
  by
  intro Γ e₀ e₁ τ ε₀ Hstep Hτ
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
  ∀ e₀ e₁ τ ε₀,
    (e₀ ⭢ e₁) →
    typing_reification ⦰ e₀ τ ε₀ →
    ∃ ε₁,
      typing_reification ⦰ e₁ τ ε₁ ∧
      ε₁ ≤ ε₀ :=
  by
  intros e₀ e₁ τ ε₀ Hstep
  apply preservation.strengthened
  apply Hstep

theorem preservation.stepn :
  ∀ e₀ e₁ τ ε₀,
    (e₀ ⭢* e₁) →
    typing_reification ⦰ e₀ τ ε₀ →
    ∃ ε₁,
      typing_reification ⦰ e₁ τ ε₁ ∧
      ε₁ ≤ ε₀ :=
  by
  intro e₀ e₁ τ ε₀ Hstepn Hτ
  induction Hstepn generalizing ε₀
  case refl => exists ε₀
  case multi Hstep _ IH =>
    have ⟨ε₁, IHτ₁, Hε₁⟩ := preservation _ _ _ _ Hstep Hτ
    have ⟨ε₂, IHτ₂, Hε₂⟩ := IH _ IHτ₁
    exists ε₂
    constructor
    . apply IHτ₂
    . apply le_trans; apply Hε₂; apply Hε₁

theorem preservation.dynamic :
  ∀ e₀ e₁ τ,
    (e₀ ⭢* e₁) →
    typing ⦰ 𝟚 e₀ τ ⊥ →
    typing ⦰ 𝟚 e₁ τ ⊥ :=
  by
  intros e₀ e₁ τ Hstepn Hτ
  have ⟨Hwbt, _⟩ := typing.dynamic_impl_pure _ _ _ _ Hτ
  have HG := typing.dynamic_impl_grounded _ _ _ _ Hτ
  have HG := grounded.under_stepn _ _ Hstepn HG
  rw [← (grounded_iff_erase_identity _).mp HG, ← (grounded_ty_iff_erase_identity _).mp Hwbt]
  have Hτ := typing.escape _ _ _ Hτ
  have Hτ := typing_reification.pure _ _ _ Hτ
  have ⟨ε, Hτ, Hε⟩ := preservation.stepn _ _ _ _ Hstepn Hτ
  cases ε <;> simp at Hε
  have Hτ := typing_reification.erase.safety _ _ _ _ Hτ
  apply Hτ
