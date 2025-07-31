import CollapsingTowers.TwoLevelBasic.LogicEquiv.Defs

theorem consistency.head :
  ∀ Γ e₀ e₁ τ φ,
    head e₀ e₁ →
    typing Γ 𝟙 e₀ τ φ →
    typing Γ 𝟙 e₁ τ φ →
    logic_equiv_typing ‖Γ‖𝛾 ‖e₀‖ ‖e₁‖ ‖τ‖𝜏 :=
  by
  intros Γ e₀ e₁ τ φ Hhead Hτ₀ Hτ₁
  cases Hhead <;> try apply typing.erase_fundamental; apply Hτ₀
  case lets Hvalue =>
    constructor; constructor
    . rw [lc, ← lc.under_erase]; apply typing.regular; apply Hτ₀
    . rw [← env.erase.length, ← closed.under_erase]
      apply typing.closed_at_env; apply Hτ₀
    constructor; constructor
    . rw [lc, ← lc.under_erase]; apply typing.regular; apply Hτ₁
    . rw [← env.erase.length, ← closed.under_erase]
      apply typing.closed_at_env; apply Hτ₁
    intros γ₀ γ₁ HsemΓ
    have ⟨Hmulti_wf₀, Hmulti_wf₁⟩ := logic_equiv_env.multi_wf _ _ _ HsemΓ
    apply logic_equiv_expr.stepn
    apply (typing.erase_fundamental _ _ _ _ _ Hτ₁).right.right; apply HsemΓ
    . apply pure_stepn.multi _ _ _ _ (pure_stepn.refl _)
      rw [comm.erase_opening_subst, comm.multi_subst_opening_value _ _ _ _ Hmulti_wf₀]
      apply pure_step.pure id; apply ctx𝕄.hole
      apply lc.under_multi_subst; apply Hmulti_wf₀; rw [← lc.under_erase]; apply typing.regular; apply Hτ₀
      simp; apply head.lets
      cases Hτ₀ with
      | lets _ _ _ _ _ _ _ _ Hτv _ HwellBinds _ =>
          apply And.left; apply logic_equiv_env.erase_value
          apply Hτv; apply HsemΓ; apply Hvalue; apply HwellBinds
    . apply pure_stepn.refl
  case app₁ Hvalue =>
    --
    --
    -- value v
    -- ——————————————————————————————————
    -- ‖Γ‖ ⊧ ‖λ.e @ v‖ ≈ ‖e⟦0 ↦ v⟧‖ : ‖τ‖
    --
    --
    -- value v
    -- (γ₀, γ₁) ∈ 𝓖⟦Γ⟧
    -- ————————————————————————————————————————
    -- (γ₀(‖λ.e @ v‖), γ₁(‖e⟦0 ↦ v⟧‖)) ∈ 𝓔⟦‖τ‖⟧
    --
    --
    -- value v
    -- (γ₀, γ₁) ∈ 𝓖⟦Γ⟧
    -- ————————————————————————————————————————————————————
    -- (λ.γ₀(‖e‖) @ γ₀(‖v‖), γ₁(‖e‖)⟦0 ↦ γ₁(‖v‖)⟧) ∈ 𝓔⟦‖τ‖⟧
    --
    --
    -- value v
    -- ————————————————————————————————————————————
    -- λ.γ₀(‖e‖) @ γ₀(‖v‖) ↦* γ₀(‖e‖)⟦0 ↦ γ₀(‖v‖)⟧
    --
    --
    -- value v
    -- —————————————
    -- value γ₀(‖v‖)
    constructor; constructor
    . rw [lc, ← lc.under_erase]; apply typing.regular; apply Hτ₀
    . rw [← env.erase.length, ← closed.under_erase]
      apply typing.closed_at_env; apply Hτ₀
    constructor; constructor
    . rw [lc, ← lc.under_erase]; apply typing.regular; apply Hτ₁
    . rw [← env.erase.length, ← closed.under_erase]
      apply typing.closed_at_env; apply Hτ₁
    intros γ₀ γ₁ HsemΓ
    have ⟨Hmulti_wf₀, Hmulti_wf₁⟩ := logic_equiv_env.multi_wf _ _ _ HsemΓ
    apply logic_equiv_expr.stepn
    apply (typing.erase_fundamental _ _ _ _ _ Hτ₁).right.right; apply HsemΓ
    . apply pure_stepn.multi _ _ _ _ (pure_stepn.refl _)
      rw [comm.erase_opening_subst, comm.multi_subst_opening_value _ _ _ _ Hmulti_wf₀]
      apply pure_step.pure id; apply ctx𝕄.hole
      apply lc.under_multi_subst; apply Hmulti_wf₀; rw [← lc.under_erase]; apply typing.regular; apply Hτ₀
      simp; apply head.app₁
      cases Hτ₀ with
      | app₁ _ _ _ _ _ _ _ _ _ Hτe Hτv =>
        cases Hτe with
        | lam _ _ _ _ _ _ _ HwellBinds =>
          apply And.left; apply logic_equiv_env.erase_value
          apply Hτv; apply HsemΓ; apply Hvalue; apply HwellBinds
    . apply pure_stepn.refl
  case lift_lam e =>
    have HEq : ‖.lam𝕔 (maping𝕔 0 e)‖ = ‖.lift (.lam e)‖ :=
      by simp [identity.erase_maping𝕔]
    rw [HEq]; apply typing.erase_fundamental; apply Hτ₀
