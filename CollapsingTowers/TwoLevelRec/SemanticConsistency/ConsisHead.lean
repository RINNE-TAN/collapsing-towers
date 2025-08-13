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

lemma consistency.lets :
  ∀ Γ e bᵥ τ φ,
    value bᵥ →
    typing Γ 𝟙 (.lets bᵥ e) τ φ →
    typing Γ 𝟙 (opening 0 bᵥ e) τ φ →
    log_equiv ‖Γ‖𝛾 ‖.lets bᵥ e‖ ‖opening 0 bᵥ e‖ ‖τ‖𝜏 :=
  by
  intros Γ e bᵥ τ φ HvalueBind Hτ₀ Hτ₁
  constructor
  -- left hand side
  . have HEτ₀ := typing.erase_safety _ _ _ _ _ Hτ₀
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
    -- (v₀, v₁) ∈ 𝓥⟦‖τ‖⟧{k - i}
    have ⟨_, _, IH⟩ := log_approx.fundamental _ _ _ HEτ₁
    simp only [log_approx_expr] at IH
    have ⟨v₁, Hstep₁, Hsem_value⟩ := IH _ _ _ HsemΓ i (by omega) _ Hvalue₀ Hstep₀
    exists v₁
    constructor
    . apply Hstep₁
    . apply log_approx_value.antimono
      apply Hsem_value; omega
  -- right hand side
  . have HEτ₀ := typing.erase_safety _ _ _ _ _ Hτ₁
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
    -- (v₀, v₁) ∈ 𝓥⟦‖τ‖⟧{k - j}
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
    -- lets x = γ₁‖bᵥ‖ in γ₁‖e‖ ⇝* v₁
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

lemma consistency.app₁ :
  ∀ Γ e argᵥ τ φ,
    value argᵥ →
    typing Γ 𝟙 (.app₁ (.lam e) argᵥ) τ φ →
    typing Γ 𝟙 (opening 0 argᵥ e) τ φ →
    log_equiv ‖Γ‖𝛾 ‖.app₁ (.lam e) argᵥ‖ ‖opening 0 argᵥ e‖ ‖τ‖𝜏 :=
  by
  intros Γ e argᵥ τ φ HvalueArg Hτ₀ Hτ₁
  constructor
  -- left hand side
  . have HEτ₀ := typing.erase_safety _ _ _ _ _ Hτ₀
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
    -- value argᵥ
    -- ———————————————————————————————
    -- value γ₀‖argᵥ‖ ∧ value γ₁‖argᵥ‖
    have ⟨HvalueArg₀, HvalueArg₁⟩ : value (multi_subst γ₀ ‖argᵥ‖) ∧ value (multi_subst γ₁ ‖argᵥ‖) :=
      by
      cases Hτ₀
      case app₁ Hτarg Hτf =>
        cases Hτf
        case lam Hwbt _ =>
          apply consistency.erase_value
          apply HvalueArg; apply Hwbt; apply Hτarg; apply HsemΓ
    --
    --
    -- value λx.e
    -- ——————————————
    -- value γ₀‖λx.e‖
    have HvalueFun₀ : value (.lam (multi_subst γ₀ ‖e‖)) :=
      by
      cases Hτ₀
      case app₁ Hτf =>
        apply value.lam
        apply lc.under_multi_subst; apply Hmulti_wf₀
        rw [← lc.under_erase]; apply typing.regular _ _ _ _ _ Hτf
    --
    --
    -- λx.γ₀‖e₀‖ @ γ₀‖argᵥ‖ ⇝ ⟦j⟧ v₀
    -- ————————————————————————————————
    -- j = i + 1
    -- (x ↦ γ₀‖argᵥ‖, γ₀)‖e‖ ⇝ ⟦i⟧ v₀
    simp at Hstep₀
    have ⟨i, HEqj, Hstep₀⟩ := stepn_indexed.refine.lam _ _ _ _ HvalueFun₀ HvalueArg₀ Hvalue₀ Hstep₀
    --
    --
    -- (x ↦ γ₀‖argᵥ‖, γ₀)‖e‖ ⇝ ⟦i⟧ v₀
    -- ———————————————————————————————
    -- γ₀‖(x ↦ argᵥ)e‖ ⇝ ⟦i⟧ v₀
    have HEq : opening 0 (multi_subst γ₀ ‖argᵥ‖) (multi_subst γ₀ ‖e‖) = multi_subst γ₀ ‖opening 0 argᵥ e‖ :=
      by rw [comm.erase_opening_value, comm.multi_subst_opening_value]; apply Hmulti_wf₀
    rw [HEq] at Hstep₀
    --
    --
    -- γ₀‖(x ↦ argᵥ)e‖ ⇝ ⟦i⟧ v₀
    -- ‖Γ‖ ⊧ ‖(x ↦ argᵥ)e‖ ≤𝑙𝑜𝑔 ‖(x ↦ argᵥ)e‖ : ‖τ‖
    -- —————————————————————————————————————————
    -- γ₁‖(x ↦ argᵥ)e‖ ⇝* v₁
    -- (v₀, v₁) ∈ 𝓥⟦‖τ‖⟧{k - i}
    have ⟨_, _, IH⟩ := log_approx.fundamental _ _ _ HEτ₁
    simp only [log_approx_expr] at IH
    have ⟨v₁, Hstep₁, Hsem_value⟩ := IH _ _ _ HsemΓ i (by omega) _ Hvalue₀ Hstep₀
    exists v₁
    constructor
    . apply Hstep₁
    . apply log_approx_value.antimono
      apply Hsem_value; omega
  -- right hand side
  . have HEτ₀ := typing.erase_safety _ _ _ _ _ Hτ₁
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
    -- γ₀‖(x ↦ argᵥ)e‖ ⇝ ⟦j⟧ v₀
    -- ‖Γ‖ ⊧ ‖(x ↦ argᵥ)e‖ ≤𝑙𝑜𝑔 ‖(x ↦ argᵥ)e‖ : ‖τ‖
    -- ————————————————————————————————————————————
    -- γ₁‖(x ↦ argᵥ)e‖ ⇝* v₁
    -- (v₀, v₁) ∈ 𝓥⟦‖τ‖⟧{k - j}
    have ⟨_, _, IH⟩ := log_approx.fundamental _ _ _ HEτ₀
    simp only [log_approx_expr] at IH
    have ⟨v₁, Hstep₁, Hsem_value⟩ := IH _ _ _ HsemΓ _ Hindexj _ Hvalue₀ Hstep₀
    --
    --
    -- γ₁‖(x ↦ argᵥ)e‖ ⇝* v₁
    -- —————————————————————————————
    -- (x ↦ γ₁‖argᵥ‖, γ₁)‖e‖ ⇝* v₁
    have HEq : multi_subst γ₁ ‖opening 0 argᵥ e‖ = opening 0 (multi_subst γ₁ ‖argᵥ‖) (multi_subst γ₁ ‖e‖) :=
      by rw [comm.erase_opening_value, comm.multi_subst_opening_value]; apply Hmulti_wf₁
    rw [HEq] at Hstep₁
    -- (x ↦ γ₁‖argᵥ‖, γ₁)‖e‖ ⇝* v₁
    -- ————————————————————————————
    -- (λx.γ₁‖e‖) @ γ₁‖argᵥ‖ ⇝* v₁
    exists v₁
    constructor
    . simp
      apply stepn.multi _ _ _ _ Hstep₁
      apply step_lvl.pure id; apply ctx𝕄.hole
      apply typing.regular; apply HSτ₁
      apply head.app₁
      --
      --
      -- value argᵥ
      -- ———————————————————————————
      -- value γ₀‖argᵥ‖ ∧ value γ₁‖argᵥ‖
      have ⟨HvalueArg₀, HvalueArg₁⟩ : value (multi_subst γ₀ ‖argᵥ‖) ∧ value (multi_subst γ₁ ‖argᵥ‖) :=
        by
        cases Hτ₀
        case app₁ Hτarg Hτf =>
          cases Hτf
          case lam Hwbt _ =>
            apply consistency.erase_value
            apply HvalueArg; apply Hwbt; apply Hτarg; apply HsemΓ
      apply HvalueArg₁
    . apply Hsem_value

lemma consistency.lift_lam :
  ∀ Γ e τ φ,
    typing Γ 𝟙 (.lift (.lam e)) τ φ →
    typing Γ 𝟙 (.lam𝕔 (maping𝕔 0 e)) τ φ →
    log_equiv ‖Γ‖𝛾 ‖.lift (.lam e)‖ ‖.lam𝕔 (maping𝕔 0 e)‖ ‖τ‖𝜏 :=
  by
  intros Γ e τ φ Hτ₀ Hτ₁
  have HEq : ‖.lam𝕔 (maping𝕔 0 e)‖ = ‖.lift (.lam e)‖ :=
    by simp [identity.erase_maping𝕔]
  rw [HEq]
  constructor
  -- left hand side
  . apply log_approx.fundamental; apply typing.erase_safety; apply Hτ₀
  -- right hand side
  . apply log_approx.fundamental; apply typing.erase_safety; apply Hτ₀

lemma consistency.fix₁ :
  ∀ Γ fᵥ τ φ,
    value fᵥ →
    typing Γ 𝟙 (.fix₁ fᵥ) τ φ →
    typing Γ 𝟙 (.lam (.app₁ (.app₁ fᵥ (.fix₁ fᵥ)) (.bvar 0))) τ φ →
    log_equiv ‖Γ‖𝛾 ‖.fix₁ fᵥ‖ ‖.lam (.app₁ (.app₁ fᵥ (.fix₁ fᵥ)) (.bvar 0))‖ ‖τ‖𝜏 :=
  by
  intros Γ fᵥ τ φ HvalueFix Hτ₀ Hτ₁
  constructor
  -- left hand side
  . have HEτ₀ := typing.erase_safety _ _ _ _ _ Hτ₀
    have HEτ₁ := typing.erase_safety _ _ _ _ _ Hτ₁
    constructor; apply HEτ₀
    constructor; apply HEτ₁
    intros k γ₀ γ₁ HsemΓ
    have ⟨Hmulti_wf₀, Hmulti_wf₁⟩ := log_approx_env.multi_wf _ _ _ _ HsemΓ
    have ⟨HSτ₀, HSτ₁⟩ := log_approx_env.multi_subst.typing _ _ _ _ _ _ _ HEτ₀ HEτ₁ HsemΓ
    simp at HSτ₀ HSτ₁
    simp only [log_approx_expr]
    intros j Hindexj v₀ Hvalue₀ Hstep₀
    simp at Hstep₀
    --
    --
    -- value fᵥ
    -- ————————————
    -- value γ₀‖fᵥ‖
    -- value γ₀‖λx.fᵥ @ (fix fᵥ) @ x‖
    have HvalueFix₀ : value (multi_subst γ₀ ‖fᵥ‖) :=
      by
      cases HvalueFix
      case lam e =>
        simp; apply value.lam
        apply lc.under_multi_subst; apply Hmulti_wf₀
        rw [← lc.under_erase]; apply typing.regular _ _ _ _ _ Hτ₀
      all_goals nomatch Hτ₀
    have HvalueFun₀ : value (multi_subst γ₀ ‖.lam (.app₁ (.app₁ fᵥ (.fix₁ fᵥ)) (.bvar 0))‖) :=
      by
      simp; apply value.lam
      simp; apply lc.inc; apply lc.value
      apply HvalueFix₀; omega
    --
    --
    -- fix γ₀‖fᵥ‖ ⇝ ⟦j⟧ v₀
    -- —————————————————————————————
    -- v₀ = γ₀‖λx.fᵥ @ (fix fᵥ) @ x‖
    have ⟨z, r, HEqj, _, Hstepr, HEqv⟩ := stepn_indexed.refine.fix₁ _ _ _ Hvalue₀ (typing.grounded_at_dyn _ _ _ _ HSτ₀) Hstep₀
    have ⟨HEqr, Hz⟩ := stepn_indexed.value_impl_termination _ _ _ HvalueFix₀ Hstepr
    --
    --
    -- ‖Γ‖ ⊧ ‖λx.fᵥ @ (fix fᵥ) @ x‖ ≤𝑙𝑜𝑔 ‖λx.fᵥ @ (fix fᵥ) @ x‖ : ‖τ‖
    -- ———————————————————————————————————————————————————————————————
    -- (γ₀‖λx.fᵥ @ (fix fᵥ) @ x‖, γ₁‖λx.fᵥ @ (fix fᵥ) @ x‖) ∈ 𝓥⟦‖τ‖⟧{k}
    have ⟨_, _, IH⟩ := log_approx.fundamental _ _ _ HEτ₁
    simp only [log_approx_expr] at IH
    have ⟨v₁, Hstep₁, Hsem_value⟩ := IH _ _ _ HsemΓ 0 (by omega) _ HvalueFun₀ (stepn_indexed.refl _)
    exists v₁
    constructor
    . apply Hstep₁
    . rw [HEqv, ← HEqr]
      simp at Hsem_value
      apply log_approx_value.antimono
      apply Hsem_value; omega
  -- right hand side
  . have HEτ₀ := typing.erase_safety _ _ _ _ _ Hτ₁
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
    -- γ₀‖λx.fᵥ @ (fix fᵥ) @ x‖ ⇝ ⟦j⟧ v₀
    -- ‖Γ‖ ⊧ ‖λx.fᵥ @ (fix fᵥ) @ x‖ ≤𝑙𝑜𝑔 ‖λx.fᵥ @ (fix fᵥ) @ x‖ : ‖τ‖
    -- —————————————————————————————————————————————————————————————
    -- γ₁‖λx.fᵥ @ (fix fᵥ) @ x‖ ⇝* v₁
    -- (v₀, v₁) ∈ 𝓥⟦‖τ‖⟧{k - j}
    have ⟨_, _, IH⟩ := log_approx.fundamental _ _ _ HEτ₀
    simp only [log_approx_expr] at IH
    have ⟨v₁, Hstep₁, Hsem_value⟩ := IH _ _ _ HsemΓ _ Hindexj _ Hvalue₀ Hstep₀
    simp at Hstep₁
    -- γ₁‖λx.fᵥ @ (fix fᵥ) @ x‖ ⇝* v₁
    -- ——————————————————————————————
    -- γ₁‖fix fᵥ‖ ⇝* v₁
    exists v₁
    constructor
    . simp
      apply stepn.multi _ _ _ _ Hstep₁
      apply step_lvl.pure id; apply ctx𝕄.hole
      apply typing.regular; apply HSτ₁
      apply head.fix₁
      --
      --
      -- value fᵥ
      -- ————————————
      -- value γ₁‖fᵥ‖
      have HvalueFix₁ : value (multi_subst γ₁ ‖fᵥ‖) :=
        by
        cases HvalueFix
        case lam e =>
          simp; apply value.lam
          apply lc.under_multi_subst; apply Hmulti_wf₁
          rw [← lc.under_erase]; apply typing.regular _ _ _ _ _ Hτ₀
        all_goals nomatch Hτ₀
      apply HvalueFix₁
    . apply Hsem_value

theorem consistency.head :
  ∀ Γ e₀ e₁ τ φ,
    head e₀ e₁ →
    typing Γ 𝟙 e₀ τ φ →
    log_equiv ‖Γ‖𝛾 ‖e₀‖ ‖e₁‖ ‖τ‖𝜏 :=
  by
  intros Γ e₀ e₁ τ φ Hhead Hτ₀
  have Hτ₁ := preservation.head _ _ _ _ _ Hhead Hτ₀
  cases Hhead
  case lets e bᵥ HvalueBind =>
    apply consistency.lets
    apply HvalueBind; apply Hτ₀; apply Hτ₁
  case app₁ e argᵥ HvalueArg =>
    apply consistency.app₁
    apply HvalueArg; apply Hτ₀; apply Hτ₁
  case lift_lam e =>
    apply consistency.lift_lam
    apply Hτ₀; apply Hτ₁
  case fix₁ fᵥ HvalueFix =>
    apply consistency.fix₁
    apply HvalueFix; apply Hτ₀; apply Hτ₁
  all_goals
    apply log_equiv.fundamental
    apply typing.erase_safety
    apply Hτ₀
