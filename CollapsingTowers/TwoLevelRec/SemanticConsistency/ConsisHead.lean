import CollapsingTowers.TwoLevelRec.LogicalEquiv.Defs
import CollapsingTowers.TwoLevelRec.Erasure.Defs

-- value v
-- —————————————
-- value γ₀(‖v‖)
--
--
-- value n  value λ.e        value (code x)  value (code e)
-- ———————  ———————————————  ——————————————  ——————————————————
-- value n  value λ.γ₀(‖e‖)  value γ₀(x)     Binding Time Error
lemma consistency.erase_value :
  ∀ k Γ v τ φ γ₀ γ₁,
    value v →
    wbt 𝟙 τ →
    typing Γ 𝟙 v τ φ →
    log_approx_env k γ₀ γ₁ ‖Γ‖𝛾 →
    value (multi_subst γ₀ ‖v‖) ∧ value (multi_subst γ₁ ‖v‖) :=
  by
  intros k Γ v τ φ γ₀ γ₁ Hvalue HwellBinds Hτ HsemΓ
  have ⟨Hmulti_wf₀, Hmulti_wf₁⟩ := log_approx_env.multi_wf _ _ _ _ HsemΓ
  cases Hvalue
  case lam Hlc =>
    simp
    constructor
    . apply value.lam
      apply lc.under_multi_subst; apply Hmulti_wf₀
      rw [← lc.under_erase]; apply Hlc
    . apply value.lam
      apply lc.under_multi_subst; apply Hmulti_wf₁
      rw [← lc.under_erase]; apply Hlc
  case lit =>
    simp; apply value.lit
  case code e _ =>
    cases e <;> cases Hτ <;> try simp at HwellBinds
    apply log_approx_value.syntactic.value
    apply log_approx_env.binds_log_approx_value
    apply HsemΓ; apply env.erase.binds; assumption

lemma consistency.head :
  ∀ Γ e₀ e₁ τ φ,
    head e₀ e₁ →
    typing Γ 𝟙 e₀ τ φ →
    log_equiv ‖Γ‖𝛾 ‖e₀‖ ‖e₁‖ ‖τ‖𝜏 :=
  by
  intros Γ e₀ e₁ τ φ Hhead Hτ₀
  have Hτ₁ := preservation.head _ _ _ _ _ Hhead Hτ₀
  constructor
  -- left hand side
  . cases Hhead <;> try apply log_approx.fundamental; apply typing.erase_safety; apply Hτ₀
    case lets e bᵥ HvalueBind =>
      have HEτ₀ := typing.erase_safety _ _ _ _ _ Hτ₀
      have HEτ₁ := typing.erase_safety _ _ _ _ _ Hτ₁
      constructor; apply HEτ₀
      constructor; apply HEτ₁
      intros k γ₀ γ₁ HsemΓ
      have ⟨Hmulti_wf₀, Hmulti_wf₁⟩ := log_approx_env.multi_wf _ _ _ _ HsemΓ
      have ⟨HSτ₀, HSτ₁⟩ := log_approx_env.multi_subst.typing _ _ _ _ _ _ _ HEτ₀ HEτ₁ HsemΓ
      simp at HSτ₀ HSτ₁
      simp only [log_approx_expr]
      intros j Hindexj v₀ Hvalue₀ Hstep₀
      --
      --
      -- value bᵥ
      -- ———————————————————————————
      -- value γ₀‖bᵥ‖ ∧ value γ₁‖bᵥ‖
      have ⟨HvalueBind₀, HvalueBind₁⟩ : value (multi_subst γ₀ ‖bᵥ‖) ∧ value (multi_subst γ₁ ‖bᵥ‖) :=
        by
        cases Hτ₀
        case lets Hwbt Hτb Hclosed Hτe =>
          apply consistency.erase_value
          apply HvalueBind; apply Hwbt; apply Hτb; apply HsemΓ
      --
      --
      -- lets x = γ₀‖bᵥ‖ in γ₀‖e‖ ⇝ ⟦j⟧ v₀
      -- —————————————————————————————————
      -- i + 1 = j
      -- (x ↦ γ₀‖bᵥ‖, γ₀)‖e‖ ⇝ ⟦i⟧ v₀
      simp at Hstep₀
      have ⟨z, i, r, HEqj, _, Hstepr, Hstep₀⟩ :=
        stepn_indexed.refine.lets _ _ _ _ Hvalue₀ (typing.grounded_at_dyn _ _ _ _ HSτ₀) Hstep₀
      have ⟨HEqv, Hz⟩ := stepn_indexed.value_impl_termination _ _ _ HvalueBind₀ Hstepr
      rw [← HEqv] at Hstep₀
      --
      --
      -- (x ↦ γ₀‖bᵥ‖, γ₀)‖e‖ ⇝ ⟦i⟧ v₀
      -- —————————————————————————————
      -- γ₀‖(x ↦ bᵥ)e‖ ⇝ ⟦i⟧ v₀
      have HEq : opening 0 (multi_subst γ₀ ‖bᵥ‖) (multi_subst γ₀ ‖e‖) = multi_subst γ₀ ‖opening 0 bᵥ e‖ :=
        by rw [comm.erase_opening_value, comm.multi_subst_opening_value]; apply Hmulti_wf₀
      rw [HEq] at Hstep₀
      --
      --
      -- γ₀‖(x ↦ bᵥ)e‖ ⇝ ⟦i⟧ v₀
      -- ‖Γ‖ ⊧ ‖(x ↦ bᵥ)e‖ ≤𝑙𝑜𝑔 ‖(x ↦ bᵥ)e‖ : ‖τ‖
      -- —————————————————————————————————————————
      -- γ₁‖(x ↦ bᵥ)e‖ ⇝* v₁
      -- (v₀, v₁) ∈ 𝓥⟦τ⟧{k - i}
      have ⟨_, _, IH⟩ := log_approx.fundamental _ _ _ HEτ₁
      simp only [log_approx_expr] at IH
      have ⟨v₁, Hstep₁, Hsem_value⟩ := IH _ _ _ HsemΓ i (by omega) _ Hvalue₀ Hstep₀
      exists v₁
      constructor
      . apply Hstep₁
      . apply log_approx_value.antimono
        apply Hsem_value; omega
    case app₁ =>
      admit
    case lift_lam e =>
      have HEq : ‖.lam𝕔 (maping𝕔 0 e)‖ = ‖.lift (.lam e)‖ :=
        by simp [identity.erase_maping𝕔]
      rw [HEq]
      apply log_approx.fundamental; apply typing.erase_safety; apply Hτ₀
    case fix₁ fᵥ HvalueFix =>
      admit
  -- right hand side
  . cases Hhead <;> try apply log_approx.fundamental; apply typing.erase_safety; apply Hτ₁
    case lets e bᵥ HvalueBind =>
      have HEτ₀ := typing.erase_safety _ _ _ _ _ Hτ₁
      have HEτ₁ := typing.erase_safety _ _ _ _ _ Hτ₀
      constructor; apply HEτ₀
      constructor; apply HEτ₁
      intros k γ₀ γ₁ HsemΓ
      have ⟨Hmulti_wf₀, Hmulti_wf₁⟩ := log_approx_env.multi_wf _ _ _ _ HsemΓ
      have ⟨HSτ₀, HSτ₁⟩ := log_approx_env.multi_subst.typing _ _ _ _ _ _ _ HEτ₀ HEτ₁ HsemΓ
      simp at HSτ₀ HSτ₁
      simp only [log_approx_expr]
      intros j Hindexj v₀ Hvalue₀ Hstep₀
      --
      --
      -- γ₀‖(x ↦ bᵥ)e‖ ⇝ ⟦j⟧ v₀
      -- ‖Γ‖ ⊧ ‖(x ↦ bᵥ)e‖ ≤𝑙𝑜𝑔 ‖(x ↦ bᵥ)e‖ : ‖τ‖
      -- —————————————————————————————————————————
      -- γ₁‖(x ↦ bᵥ)e‖ ⇝* v₁
      -- (v₀, v₁) ∈ 𝓥⟦τ⟧{k - j}
      have ⟨_, _, IH⟩ := log_approx.fundamental _ _ _ HEτ₀
      simp only [log_approx_expr] at IH
      have ⟨v₁, Hstep₁, Hsem_value⟩ := IH _ _ _ HsemΓ _ Hindexj _ Hvalue₀ Hstep₀
      --
      --
      -- γ₁‖(x ↦ bᵥ)e‖ ⇝* v₁
      -- —————————————————————————————
      -- (x ↦ γ₁‖bᵥ‖, γ₁)‖e‖ ⇝* v₁
      have HEq : multi_subst γ₁ ‖opening 0 bᵥ e‖ = opening 0 (multi_subst γ₁ ‖bᵥ‖) (multi_subst γ₁ ‖e‖) :=
        by rw [comm.erase_opening_value, comm.multi_subst_opening_value]; apply Hmulti_wf₁
      rw [HEq] at Hstep₁
      -- (x ↦ γ₁‖bᵥ‖, γ₁)‖e‖ ⇝* v₁
      -- —————————————————————————————————
      -- lets x = γ₁‖bᵥ‖ in γ₁‖e‖ ⇝* v₀
      exists v₁
      constructor
      . simp
        apply stepn.multi _ _ _ _ Hstep₁
        apply step_lvl.pure id; apply ctx𝕄.hole
        apply typing.regular; apply HSτ₁
        apply head.lets
        --
        --
        -- value bᵥ
        -- ———————————————————————————
        -- value γ₀‖bᵥ‖ ∧ value γ₁‖bᵥ‖
        have ⟨HvalueBind₀, HvalueBind₁⟩ : value (multi_subst γ₀ ‖bᵥ‖) ∧ value (multi_subst γ₁ ‖bᵥ‖) :=
          by
          cases Hτ₀
          case lets Hwbt Hτb Hclosed Hτe =>
            apply consistency.erase_value
            apply HvalueBind; apply Hwbt; apply Hτb; apply HsemΓ
        apply HvalueBind₁
      . apply Hsem_value
    case app₁ =>
      admit
    case lift_lam e =>
      have HEq : ‖.lam𝕔 (maping𝕔 0 e)‖ = ‖.lift (.lam e)‖ :=
        by simp [identity.erase_maping𝕔]
      rw [← HEq]
      apply log_approx.fundamental; apply typing.erase_safety; apply Hτ₁
    case fix₁ fᵥ HvalueFix =>
      admit
