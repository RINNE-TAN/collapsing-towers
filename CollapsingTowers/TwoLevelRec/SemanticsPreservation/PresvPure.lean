import CollapsingTowers.TwoLevelRec.LogicalEquiv.Defs

-- value v
-- —————————————
-- value γ₀(‖v‖)
--
--
-- value n  value λ.e        value (code x)  value (code e)
-- ———————  ———————————————  ——————————————  ——————————————————
-- value n  value λ.γ₀(‖e‖)  value γ₀(x)     Binding Time Error
lemma semantics_preservation.erase_value :
  ∀ k Γ v τ φ γ₀ γ₁,
    value v →
    wbt 𝟙 τ →
    typing Γ 𝟙 v τ φ →
    log_approx_env k γ₀ γ₁ (erase_env Γ) →
    value (msubst γ₀ ‖v‖) ∧ value (msubst γ₁ ‖v‖) :=
  by
  intros k Γ v τ φ γ₀ γ₁ Hvalue HwellBinds Hτ HsemΓ
  have ⟨Hmwf₀, Hmwf₁⟩ := log_approx_env.mwf _ _ _ _ HsemΓ
  cases Hvalue
  case lam Hlc =>
    simp
    constructor
    . apply value.lam
      apply lc.under_msubst; apply Hmwf₀
      rw [← lc.under_erase]; apply Hlc
    . apply value.lam
      apply lc.under_msubst; apply Hmwf₁
      rw [← lc.under_erase]; apply Hlc
  case lit =>
    simp; apply value.lit
  case code e _ =>
    cases e <;> cases Hτ <;> try simp at HwellBinds
    apply log_approx_value.syntactic.value
    apply log_approx_env.binds_log_approx_value
    apply HsemΓ; apply erase_env.binds; assumption

lemma semantics_preservation.lets :
  ∀ Γ e bᵥ τ φ₀ φ₁,
    value bᵥ →
    typing Γ 𝟙 (.lets bᵥ e) τ φ₀ →
    typing Γ 𝟙 (opening 0 bᵥ e) τ φ₁ →
    log_equiv (erase_env Γ) ‖.lets bᵥ e‖ ‖opening 0 bᵥ e‖ (erase_ty τ) :=
  by
  intros Γ e bᵥ τ φ₀ φ₁ HvalueBind Hτ₀ Hτ₁
  constructor
  -- left approximation
  . have HEτ₀ := typing.erase.safety _ _ _ _ _ Hτ₀
    have HEτ₁ := typing.erase.safety _ _ _ _ _ Hτ₁
    constructor; apply HEτ₀
    constructor; apply HEτ₁
    intros k γ₀ γ₁ HsemΓ
    have ⟨Hmwf₀, Hmwf₁⟩ := log_approx_env.mwf _ _ _ _ HsemΓ
    have ⟨HSτ₀, HSτ₁⟩ := log_approx_env.msubst.typing _ _ _ _ _ _ _ HEτ₀ HEτ₁ HsemΓ
    simp at HSτ₀ HSτ₁
    simp only [log_approx_expr]
    intros j Hindexj v₀ Hvalue₀ Hstep₀
    --
    --
    -- value bᵥ
    -- ———————————————————————————
    -- value γ₀‖bᵥ‖ ∧ value γ₁‖bᵥ‖
    have ⟨HvalueBind₀, HvalueBind₁⟩ : value (msubst γ₀ ‖bᵥ‖) ∧ value (msubst γ₁ ‖bᵥ‖) :=
      by
      cases Hτ₀
      case lets Hwbt Hτb Hclosed Hτe =>
        apply semantics_preservation.erase_value
        apply HvalueBind; apply Hwbt; apply Hτb; apply HsemΓ
    --
    --
    -- lets x = γ₀‖bᵥ‖ in γ₀‖e‖ ⇝ ⟦j⟧ v₀
    -- —————————————————————————————————
    -- i + 1 = j
    -- (x ↦ γ₀‖bᵥ‖, γ₀)‖e‖ ⇝ ⟦i⟧ v₀
    simp at Hstep₀
    have ⟨z, i, r, HEqj, _, Hstepr, Hstep₀⟩ :=
      stepn_indexed.refine.lets _ _ _ _ Hvalue₀ (typing.dynamic_impl_grounded _ _ _ _ HSτ₀) Hstep₀
    have ⟨HEqv, Hz⟩ := stepn_indexed.value_impl_termination _ _ _ HvalueBind₀ Hstepr
    rw [← HEqv] at Hstep₀
    --
    --
    -- (x ↦ γ₀‖bᵥ‖, γ₀)‖e‖ ⇝ ⟦i⟧ v₀
    -- —————————————————————————————
    -- γ₀‖(x ↦ bᵥ)e‖ ⇝ ⟦i⟧ v₀
    have HEq : opening 0 (msubst γ₀ ‖bᵥ‖) (msubst γ₀ ‖e‖) = msubst γ₀ ‖opening 0 bᵥ e‖ :=
      by rw [comm.erase_opening_value, comm.msubst_opening_value]; apply Hmwf₀
    rw [HEq] at Hstep₀
    --
    --
    -- γ₀‖(x ↦ bᵥ)e‖ ⇝ ⟦i⟧ v₀
    -- ‖Γ‖ ⊧ ‖(x ↦ bᵥ)e‖ ≤𝑙𝑜𝑔 ‖(x ↦ bᵥ)e‖ : ‖τ‖
    -- —————————————————————————————————————————
    -- γ₁‖(x ↦ bᵥ)e‖ ⇝* v₁
    -- (k - i, v₀, v₁) ∈ 𝓥⟦‖τ‖⟧
    have ⟨_, _, IH⟩ := log_approx.fundamental _ _ _ HEτ₁
    simp only [log_approx_expr] at IH
    have ⟨v₁, Hstep₁, Hsem_value⟩ := IH _ _ _ HsemΓ i (by omega) _ Hvalue₀ Hstep₀
    exists v₁
    constructor
    . apply Hstep₁
    . apply log_approx_value.antimono
      apply Hsem_value; omega
  -- right approximation
  . have HEτ₀ := typing.erase.safety _ _ _ _ _ Hτ₁
    have HEτ₁ := typing.erase.safety _ _ _ _ _ Hτ₀
    constructor; apply HEτ₀
    constructor; apply HEτ₁
    intros k γ₀ γ₁ HsemΓ
    have ⟨Hmwf₀, Hmwf₁⟩ := log_approx_env.mwf _ _ _ _ HsemΓ
    have ⟨HSτ₀, HSτ₁⟩ := log_approx_env.msubst.typing _ _ _ _ _ _ _ HEτ₀ HEτ₁ HsemΓ
    simp at HSτ₀ HSτ₁
    simp only [log_approx_expr]
    intros j Hindexj v₀ Hvalue₀ Hstep₀
    --
    --
    -- γ₀‖(x ↦ bᵥ)e‖ ⇝ ⟦j⟧ v₀
    -- ‖Γ‖ ⊧ ‖(x ↦ bᵥ)e‖ ≤𝑙𝑜𝑔 ‖(x ↦ bᵥ)e‖ : ‖τ‖
    -- —————————————————————————————————————————
    -- γ₁‖(x ↦ bᵥ)e‖ ⇝* v₁
    -- (k - j, v₀, v₁) ∈ 𝓥⟦‖τ‖⟧
    have ⟨_, _, IH⟩ := log_approx.fundamental _ _ _ HEτ₀
    simp only [log_approx_expr] at IH
    have ⟨v₁, Hstep₁, Hsem_value⟩ := IH _ _ _ HsemΓ _ Hindexj _ Hvalue₀ Hstep₀
    --
    --
    -- γ₁‖(x ↦ bᵥ)e‖ ⇝* v₁
    -- —————————————————————————————
    -- (x ↦ γ₁‖bᵥ‖, γ₁)‖e‖ ⇝* v₁
    have HEq : msubst γ₁ ‖opening 0 bᵥ e‖ = opening 0 (msubst γ₁ ‖bᵥ‖) (msubst γ₁ ‖e‖) :=
      by rw [comm.erase_opening_value, comm.msubst_opening_value]; apply Hmwf₁
    rw [HEq] at Hstep₁
    --
    --
    -- (x ↦ γ₁‖bᵥ‖, γ₁)‖e‖ ⇝* v₁
    -- —————————————————————————————————
    -- lets x = γ₁‖bᵥ‖ in γ₁‖e‖ ⇝* v₁
    exists v₁
    constructor
    . simp
      apply stepn.multi _ _ _ _ Hstep₁
      apply step_lvl.pure _ _ _ ctx𝕄.hole
      apply typing.regular; apply HSτ₁
      apply head.lets
      --
      --
      -- value bᵥ
      -- ———————————————————————————
      -- value γ₀‖bᵥ‖ ∧ value γ₁‖bᵥ‖
      have ⟨HvalueBind₀, HvalueBind₁⟩ : value (msubst γ₀ ‖bᵥ‖) ∧ value (msubst γ₁ ‖bᵥ‖) :=
        by
        cases Hτ₀
        case lets Hwbt Hτb Hclosed Hτe =>
          apply semantics_preservation.erase_value
          apply HvalueBind; apply Hwbt; apply Hτb; apply HsemΓ
      apply HvalueBind₁
    . apply Hsem_value

lemma semantics_preservation.app₁ :
  ∀ Γ e argᵥ τ φ₀ φ₁,
    value argᵥ →
    typing Γ 𝟙 (.app₁ (.lam e) argᵥ) τ φ₀ →
    typing Γ 𝟙 (opening 0 argᵥ e) τ φ₁ →
    log_equiv (erase_env Γ) ‖.app₁ (.lam e) argᵥ‖ ‖opening 0 argᵥ e‖ (erase_ty τ) :=
  by
  intros Γ e argᵥ τ φ₀ φ₁ HvalueArg Hτ₀ Hτ₁
  constructor
  -- left approximation
  . have HEτ₀ := typing.erase.safety _ _ _ _ _ Hτ₀
    have HEτ₁ := typing.erase.safety _ _ _ _ _ Hτ₁
    constructor; apply HEτ₀
    constructor; apply HEτ₁
    intros k γ₀ γ₁ HsemΓ
    have ⟨Hmwf₀, Hmwf₁⟩ := log_approx_env.mwf _ _ _ _ HsemΓ
    have ⟨HSτ₀, HSτ₁⟩ := log_approx_env.msubst.typing _ _ _ _ _ _ _ HEτ₀ HEτ₁ HsemΓ
    simp at HSτ₀ HSτ₁
    simp only [log_approx_expr]
    intros j Hindexj v₀ Hvalue₀ Hstep₀
    --
    --
    -- value argᵥ
    -- ———————————————————————————————
    -- value γ₀‖argᵥ‖ ∧ value γ₁‖argᵥ‖
    have ⟨HvalueArg₀, HvalueArg₁⟩ : value (msubst γ₀ ‖argᵥ‖) ∧ value (msubst γ₁ ‖argᵥ‖) :=
      by
      cases Hτ₀
      case app₁ Hτarg Hτf =>
        cases Hτf
        case lam Hwbt _ =>
          apply semantics_preservation.erase_value
          apply HvalueArg; apply Hwbt; apply Hτarg; apply HsemΓ
    --
    --
    -- value λx.e
    -- ——————————————
    -- value γ₀‖λx.e‖
    have HvalueFun₀ : value (.lam (msubst γ₀ ‖e‖)) :=
      by
      cases Hτ₀
      case app₁ Hτf =>
        apply value.lam
        apply lc.under_msubst; apply Hmwf₀
        rw [← lc.under_erase]; apply typing.regular _ _ _ _ _ Hτf
    --
    --
    -- λx.γ₀‖e₀‖ @ γ₀‖argᵥ‖ ⇝ ⟦j⟧ v₀
    -- ————————————————————————————————
    -- j = i + 1
    -- (x ↦ γ₀‖argᵥ‖, γ₀)‖e‖ ⇝ ⟦i⟧ v₀
    simp at Hstep₀
    have ⟨i, HEqj, Hstep₀⟩ := stepn_indexed.refine.app₁.eliminator _ _ _ _ HvalueFun₀ HvalueArg₀ Hvalue₀ Hstep₀
    --
    --
    -- (x ↦ γ₀‖argᵥ‖, γ₀)‖e‖ ⇝ ⟦i⟧ v₀
    -- ———————————————————————————————
    -- γ₀‖(x ↦ argᵥ)e‖ ⇝ ⟦i⟧ v₀
    have HEq : opening 0 (msubst γ₀ ‖argᵥ‖) (msubst γ₀ ‖e‖) = msubst γ₀ ‖opening 0 argᵥ e‖ :=
      by rw [comm.erase_opening_value, comm.msubst_opening_value]; apply Hmwf₀
    rw [HEq] at Hstep₀
    --
    --
    -- γ₀‖(x ↦ argᵥ)e‖ ⇝ ⟦i⟧ v₀
    -- ‖Γ‖ ⊧ ‖(x ↦ argᵥ)e‖ ≤𝑙𝑜𝑔 ‖(x ↦ argᵥ)e‖ : ‖τ‖
    -- —————————————————————————————————————————
    -- γ₁‖(x ↦ argᵥ)e‖ ⇝* v₁
    -- (k - i, v₀, v₁) ∈ 𝓥⟦‖τ‖⟧
    have ⟨_, _, IH⟩ := log_approx.fundamental _ _ _ HEτ₁
    simp only [log_approx_expr] at IH
    have ⟨v₁, Hstep₁, Hsem_value⟩ := IH _ _ _ HsemΓ i (by omega) _ Hvalue₀ Hstep₀
    exists v₁
    constructor
    . apply Hstep₁
    . apply log_approx_value.antimono
      apply Hsem_value; omega
  -- right approximation
  . have HEτ₀ := typing.erase.safety _ _ _ _ _ Hτ₁
    have HEτ₁ := typing.erase.safety _ _ _ _ _ Hτ₀
    constructor; apply HEτ₀
    constructor; apply HEτ₁
    intros k γ₀ γ₁ HsemΓ
    have ⟨Hmwf₀, Hmwf₁⟩ := log_approx_env.mwf _ _ _ _ HsemΓ
    have ⟨HSτ₀, HSτ₁⟩ := log_approx_env.msubst.typing _ _ _ _ _ _ _ HEτ₀ HEτ₁ HsemΓ
    simp at HSτ₀ HSτ₁
    simp only [log_approx_expr]
    intros j Hindexj v₀ Hvalue₀ Hstep₀
    --
    --
    -- γ₀‖(x ↦ argᵥ)e‖ ⇝ ⟦j⟧ v₀
    -- ‖Γ‖ ⊧ ‖(x ↦ argᵥ)e‖ ≤𝑙𝑜𝑔 ‖(x ↦ argᵥ)e‖ : ‖τ‖
    -- ————————————————————————————————————————————
    -- γ₁‖(x ↦ argᵥ)e‖ ⇝* v₁
    -- (k - j, v₀, v₁) ∈ 𝓥⟦‖τ‖⟧
    have ⟨_, _, IH⟩ := log_approx.fundamental _ _ _ HEτ₀
    simp only [log_approx_expr] at IH
    have ⟨v₁, Hstep₁, Hsem_value⟩ := IH _ _ _ HsemΓ _ Hindexj _ Hvalue₀ Hstep₀
    --
    --
    -- γ₁‖(x ↦ argᵥ)e‖ ⇝* v₁
    -- —————————————————————————————
    -- (x ↦ γ₁‖argᵥ‖, γ₁)‖e‖ ⇝* v₁
    have HEq : msubst γ₁ ‖opening 0 argᵥ e‖ = opening 0 (msubst γ₁ ‖argᵥ‖) (msubst γ₁ ‖e‖) :=
      by rw [comm.erase_opening_value, comm.msubst_opening_value]; apply Hmwf₁
    rw [HEq] at Hstep₁
    --
    --
    -- (x ↦ γ₁‖argᵥ‖, γ₁)‖e‖ ⇝* v₁
    -- ————————————————————————————
    -- (λx.γ₁‖e‖) @ γ₁‖argᵥ‖ ⇝* v₁
    exists v₁
    constructor
    . simp
      apply stepn.multi _ _ _ _ Hstep₁
      apply step_lvl.pure _ _ _ ctx𝕄.hole
      apply typing.regular; apply HSτ₁
      apply head.app₁
      --
      --
      -- value argᵥ
      -- ———————————————————————————————
      -- value γ₀‖argᵥ‖ ∧ value γ₁‖argᵥ‖
      have ⟨HvalueArg₀, HvalueArg₁⟩ : value (msubst γ₀ ‖argᵥ‖) ∧ value (msubst γ₁ ‖argᵥ‖) :=
        by
        cases Hτ₀
        case app₁ Hτarg Hτf =>
          cases Hτf
          case lam Hwbt _ =>
            apply semantics_preservation.erase_value
            apply HvalueArg; apply Hwbt; apply Hτarg; apply HsemΓ
      apply HvalueArg₁
    . apply Hsem_value

lemma semantics_preservation.binary₁ :
  ∀ Γ op l r τ φ₀ φ₁,
    typing Γ 𝟙 (.binary₁ op (.lit l) (.lit r)) τ φ₀ →
    typing Γ 𝟙 (.lit (eval op l r)) τ φ₁ →
    log_equiv (erase_env Γ) ‖.binary₁ op (.lit l) (.lit r)‖ ‖.lit (eval op l r)‖ (erase_ty τ) :=
  by
  intros Γ op l r τ φ₀ φ₁ Hτ₀ Hτ₁
  cases τ <;> try contradiction
  constructor
  -- left approximation
  . have HEτ₀ := typing.erase.safety _ _ _ _ _ Hτ₀
    have HEτ₁ := typing.erase.safety _ _ _ _ _ Hτ₁
    constructor; apply HEτ₀
    constructor; apply HEτ₁
    intros k γ₀ γ₁ HsemΓ
    simp only [log_approx_expr]
    intros j Hindexj v₀ Hvalue₀ Hstep₀
    exists .lit (eval op l r)
    constructor
    . simp; apply stepn.refl
    . simp at Hstep₀
      have ⟨_, HEqv₀⟩ := stepn_indexed.refine.binary₁.eliminator _ _ _ _ _ Hvalue₀ Hstep₀
      simp [HEqv₀]
  -- right approximation
  . have HEτ₀ := typing.erase.safety _ _ _ _ _ Hτ₁
    have HEτ₁ := typing.erase.safety _ _ _ _ _ Hτ₀
    constructor; apply HEτ₀
    constructor; apply HEτ₁
    intros k γ₀ γ₁ HsemΓ
    simp only [log_approx_expr]
    intros j Hindexj v₀ Hvalue₀ Hstep₀
    exists .lit (eval op l r)
    constructor
    . apply stepn.multi _ _ _ _ (stepn.refl _)
      apply step_lvl.pure _ _ _ ctx𝕄.hole
      . simp
      . simp [- eval]; apply head.binary₁
    . simp [- eval] at Hstep₀
      have ⟨HEqv, Hz⟩ := stepn_indexed.value_impl_termination _ _ _ (value.lit _) Hstep₀
      simp [← HEqv]

lemma semantics_preservation.lift_lam :
  ∀ Γ e τ φ₀ φ₁,
    typing Γ 𝟙 (.lift (.lam e)) τ φ₀ →
    typing Γ 𝟙 (.lam𝕔 (codify 0 e)) τ φ₁ →
    log_equiv (erase_env Γ) ‖.lift (.lam e)‖ ‖.lam𝕔 (codify 0 e)‖ (erase_ty τ) :=
  by
  intros Γ e τ φ₀ φ₁ Hτ₀ Hτ₁
  have HEq : ‖.lam𝕔 (codify 0 e)‖ = ‖.lift (.lam e)‖ :=
    by simp [identity.erase_codify]
  rw [HEq]
  constructor
  -- left approximation
  . apply log_approx.fundamental; apply typing.erase.safety; apply Hτ₀
  -- right approximation
  . apply log_approx.fundamental; apply typing.erase.safety; apply Hτ₀

lemma semantics_preservation.fix₁ :
  ∀ Γ fᵥ τ φ₀ φ₁,
    value fᵥ →
    typing Γ 𝟙 (.fix₁ fᵥ) τ φ₀ →
    typing Γ 𝟙 (.lam (.app₁ (.app₁ fᵥ (.fix₁ fᵥ)) (.bvar 0))) τ φ₁ →
    log_equiv (erase_env Γ) ‖.fix₁ fᵥ‖ ‖.lam (.app₁ (.app₁ fᵥ (.fix₁ fᵥ)) (.bvar 0))‖ (erase_ty τ) :=
  by
  intros Γ fᵥ τ φ₀ φ₁ HvalueFix Hτ₀ Hτ₁
  constructor
  -- left approximation
  . have HEτ₀ := typing.erase.safety _ _ _ _ _ Hτ₀
    have HEτ₁ := typing.erase.safety _ _ _ _ _ Hτ₁
    constructor; apply HEτ₀
    constructor; apply HEτ₁
    intros k γ₀ γ₁ HsemΓ
    have ⟨Hmwf₀, Hmwf₁⟩ := log_approx_env.mwf _ _ _ _ HsemΓ
    have ⟨HSτ₀, HSτ₁⟩ := log_approx_env.msubst.typing _ _ _ _ _ _ _ HEτ₀ HEτ₁ HsemΓ
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
    have HvalueFix₀ : value (msubst γ₀ ‖fᵥ‖) :=
      by
      cases HvalueFix
      case lam e =>
        simp; apply value.lam
        apply lc.under_msubst; apply Hmwf₀
        rw [← lc.under_erase]; apply typing.regular _ _ _ _ _ Hτ₀
      all_goals nomatch Hτ₀
    have HvalueFun₀ : value (msubst γ₀ ‖.lam (.app₁ (.app₁ fᵥ (.fix₁ fᵥ)) (.bvar 0))‖) :=
      by
      simp; apply value.lam
      simp; apply lc.inc; apply lc.value
      apply HvalueFix₀; omega
    --
    --
    -- fix γ₀‖fᵥ‖ ⇝ ⟦j⟧ v₀
    -- —————————————————————————————
    -- v₀ = γ₀‖λx.fᵥ @ (fix fᵥ) @ x‖
    have ⟨z, r, HEqj, _, Hstepr, HEqv⟩ := stepn_indexed.refine.fix₁.constructor _ _ _ Hvalue₀ (typing.dynamic_impl_grounded _ _ _ _ HSτ₀) Hstep₀
    have ⟨HEqr, Hz⟩ := stepn_indexed.value_impl_termination _ _ _ HvalueFix₀ Hstepr
    --
    --
    -- ‖Γ‖ ⊧ ‖λx.fᵥ @ (fix fᵥ) @ x‖ ≤𝑙𝑜𝑔 ‖λx.fᵥ @ (fix fᵥ) @ x‖ : ‖τ‖
    -- ———————————————————————————————————————————————————————————————
    -- (k, γ₀‖λx.fᵥ @ (fix fᵥ) @ x‖, γ₁‖λx.fᵥ @ (fix fᵥ) @ x‖) ∈ 𝓥⟦‖τ‖⟧
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
  -- right approximation
  . have HEτ₀ := typing.erase.safety _ _ _ _ _ Hτ₁
    have HEτ₁ := typing.erase.safety _ _ _ _ _ Hτ₀
    constructor; apply HEτ₀
    constructor; apply HEτ₁
    intros k γ₀ γ₁ HsemΓ
    have ⟨Hmwf₀, Hmwf₁⟩ := log_approx_env.mwf _ _ _ _ HsemΓ
    have ⟨HSτ₀, HSτ₁⟩ := log_approx_env.msubst.typing _ _ _ _ _ _ _ HEτ₀ HEτ₁ HsemΓ
    simp at HSτ₀ HSτ₁
    simp only [log_approx_expr]
    intros j Hindexj v₀ Hvalue₀ Hstep₀
    --
    --
    -- γ₀‖λx.fᵥ @ (fix fᵥ) @ x‖ ⇝ ⟦j⟧ v₀
    -- ‖Γ‖ ⊧ ‖λx.fᵥ @ (fix fᵥ) @ x‖ ≤𝑙𝑜𝑔 ‖λx.fᵥ @ (fix fᵥ) @ x‖ : ‖τ‖
    -- —————————————————————————————————————————————————————————————
    -- γ₁‖λx.fᵥ @ (fix fᵥ) @ x‖ ⇝* v₁
    -- (k - j, v₀, v₁) ∈ 𝓥⟦‖τ‖⟧
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
      apply step_lvl.pure _ _ _ ctx𝕄.hole
      apply typing.regular; apply HSτ₁
      apply head.fix₁
      --
      --
      -- value fᵥ
      -- ————————————
      -- value γ₁‖fᵥ‖
      have HvalueFix₁ : value (msubst γ₁ ‖fᵥ‖) :=
        by
        cases HvalueFix
        case lam e =>
          simp; apply value.lam
          apply lc.under_msubst; apply Hmwf₁
          rw [← lc.under_erase]; apply typing.regular _ _ _ _ _ Hτ₀
        all_goals nomatch Hτ₀
      apply HvalueFix₁
    . apply Hsem_value

lemma semantics_preservation.ifz₁_then :
  ∀ Γ l r τ φ₀ φ₁,
    typing Γ 𝟙 (.ifz₁ (.lit 0) l r) τ φ₀ →
    typing Γ 𝟙 l τ φ₁ →
    log_equiv (erase_env Γ) ‖.ifz₁ (.lit 0) l r‖ ‖l‖ (erase_ty τ) :=
  by
  intros Γ l r τ φ₀ φ₁ Hτ₀ Hτ₁
  constructor
  -- left approximation
  . have HEτ₀ := typing.erase.safety _ _ _ _ _ Hτ₀
    have HEτ₁ := typing.erase.safety _ _ _ _ _ Hτ₁
    constructor; apply HEτ₀
    constructor; apply HEτ₁
    intros k γ₀ γ₁ HsemΓ
    simp only [log_approx_expr]
    intros j Hindexj v₀ Hvalue₀ Hstep₀
    --
    --
    -- if 0 then γ₀‖l‖ else γ₀‖r‖ ⇝ ⟦j⟧ v₀
    -- ———————————————————————————————————
    -- i + 1 = j
    -- γ₀‖l‖ ⇝* v₀
    simp at Hstep₀
    have ⟨i, HEqj, Hstep₀⟩ := stepn_indexed.refine.ifz₁_then.eliminator _ _ _ _ Hvalue₀ Hstep₀
    --
    --
    -- γ₀‖l‖ ⇝* v₀
    -- ‖Γ‖ ⊧ ‖l‖ ≤𝑙𝑜𝑔 ‖l‖ : ‖τ‖
    -- ————————————————————————
    -- γ₁‖l‖ ⇝* v₁
    -- (k - i, v₀, v₁) ∈ 𝓥⟦‖τ‖⟧
    have ⟨_, _, IH⟩ := log_approx.fundamental _ _ _ HEτ₁
    simp only [log_approx_expr] at IH
    have ⟨v₁, Hstep₁, Hsem_value⟩ := IH _ _ _ HsemΓ i (by omega) _ Hvalue₀ Hstep₀
    exists v₁
    constructor
    . apply Hstep₁
    . apply log_approx_value.antimono
      apply Hsem_value; omega
  -- right approximation
  . have HEτ₀ := typing.erase.safety _ _ _ _ _ Hτ₁
    have HEτ₁ := typing.erase.safety _ _ _ _ _ Hτ₀
    constructor; apply HEτ₀
    constructor; apply HEτ₁
    intros k γ₀ γ₁ HsemΓ
    have ⟨HSτ₀, HSτ₁⟩ := log_approx_env.msubst.typing _ _ _ _ _ _ _ HEτ₀ HEτ₁ HsemΓ
    simp only [log_approx_expr]
    intros j Hindexj v₀ Hvalue₀ Hstep₀
    --
    --
    -- γ₀‖l‖ ⇝ ⟦j⟧ v₀
    -- ‖Γ‖ ⊧ ‖l‖ ≤𝑙𝑜𝑔 ‖l‖ : ‖τ‖
    -- ————————————————————————
    -- γ₁‖l‖ ⇝* v₁
    -- (k - j, v₀, v₁) ∈ 𝓥⟦‖τ‖⟧
    have ⟨_, _, IH⟩ := log_approx.fundamental _ _ _ HEτ₀
    simp only [log_approx_expr] at IH
    have ⟨v₁, Hstep₁, Hsem_value⟩ := IH _ _ _ HsemΓ j (by omega) _ Hvalue₀ Hstep₀
    exists v₁
    constructor
    . apply stepn.multi _ _ _ _ Hstep₁
      apply step_lvl.pure _ _ _ ctx𝕄.hole
      . apply typing.regular _ _ _ _ _ HSτ₁
      . simp; apply head.ifz₁_then
    . apply Hsem_value

lemma semantics_preservation.ifz₁_else :
  ∀ Γ n l r τ φ₀ φ₁,
    typing Γ 𝟙 (.ifz₁ (.lit (n + 1)) l r) τ φ₀ →
    typing Γ 𝟙 r τ φ₁ →
    log_equiv (erase_env Γ) ‖.ifz₁ (.lit (n + 1)) l r‖ ‖r‖ (erase_ty τ) :=
  by
  intros Γ n l r τ φ₀ φ₁ Hτ₀ Hτ₁
  constructor
  -- left approximation
  . have HEτ₀ := typing.erase.safety _ _ _ _ _ Hτ₀
    have HEτ₁ := typing.erase.safety _ _ _ _ _ Hτ₁
    constructor; apply HEτ₀
    constructor; apply HEτ₁
    intros k γ₀ γ₁ HsemΓ
    simp only [log_approx_expr]
    intros j Hindexj v₀ Hvalue₀ Hstep₀
    --
    --
    -- if (n + 1) then γ₀‖l‖ else γ₀‖r‖ ⇝ ⟦j⟧ v₀
    -- —————————————————————————————————————————
    -- i + 1 = j
    -- γ₀‖r‖ ⇝* v₀
    simp at Hstep₀
    have ⟨i, HEqj, Hstep₀⟩ := stepn_indexed.refine.ifz₁_else.eliminator _ _ _ _ _ Hvalue₀ Hstep₀
    --
    --
    -- γ₀‖r‖ ⇝* v₁
    -- ‖Γ‖ ⊧ ‖r‖ ≤𝑙𝑜𝑔 ‖r‖ : ‖τ‖
    -- ————————————————————————
    -- γ₁‖r‖ ⇝* v₁
    -- (k - i, v₀, v₁) ∈ 𝓥⟦‖τ‖⟧
    have ⟨_, _, IH⟩ := log_approx.fundamental _ _ _ HEτ₁
    simp only [log_approx_expr] at IH
    have ⟨v₁, Hstep₁, Hsem_value⟩ := IH _ _ _ HsemΓ i (by omega) _ Hvalue₀ Hstep₀
    exists v₁
    constructor
    . apply Hstep₁
    . apply log_approx_value.antimono
      apply Hsem_value; omega
  -- right approximation
  . have HEτ₀ := typing.erase.safety _ _ _ _ _ Hτ₁
    have HEτ₁ := typing.erase.safety _ _ _ _ _ Hτ₀
    constructor; apply HEτ₀
    constructor; apply HEτ₁
    intros k γ₀ γ₁ HsemΓ
    have ⟨HSτ₀, HSτ₁⟩ := log_approx_env.msubst.typing _ _ _ _ _ _ _ HEτ₀ HEτ₁ HsemΓ
    simp only [log_approx_expr]
    intros j Hindexj v₀ Hvalue₀ Hstep₀
    --
    --
    -- γ₀‖r‖ ⇝ ⟦j⟧ v₁
    -- ‖Γ‖ ⊧ ‖r‖ ≤𝑙𝑜𝑔 ‖r‖ : ‖τ‖
    -- ————————————————————————
    -- γ₁‖r‖ ⇝* v₁
    -- (k - j, v₀, v₁) ∈ 𝓥⟦‖τ‖⟧
    have ⟨_, _, IH⟩ := log_approx.fundamental _ _ _ HEτ₀
    simp only [log_approx_expr] at IH
    have ⟨v₁, Hstep₁, Hsem_value⟩ := IH _ _ _ HsemΓ j (by omega) _ Hvalue₀ Hstep₀
    exists v₁
    constructor
    . apply stepn.multi _ _ _ _ Hstep₁
      apply step_lvl.pure _ _ _ ctx𝕄.hole
      . apply typing.regular _ _ _ _ _ HSτ₁
      . simp; apply head.ifz₁_else
    . apply Hsem_value

theorem semantics_preservation.pure.head :
  ∀ Γ e₀ e₁ τ φ,
    head e₀ e₁ →
    typing Γ 𝟙 e₀ τ φ →
    log_equiv (erase_env Γ) ‖e₀‖ ‖e₁‖ (erase_ty τ) :=
  by
  intros Γ e₀ e₁ τ φ Hhead Hτ₀
  have ⟨_, Hτ₁, _⟩ := preservation.pure.head _ _ _ _ _ Hhead Hτ₀
  cases Hhead
  case lets e bᵥ HvalueBind =>
    apply semantics_preservation.lets
    apply HvalueBind; apply Hτ₀; apply Hτ₁
  case app₁ e argᵥ HvalueArg =>
    apply semantics_preservation.app₁
    apply HvalueArg; apply Hτ₀; apply Hτ₁
  case binary₁ =>
    apply semantics_preservation.binary₁
    apply Hτ₀; apply Hτ₁
  case lift_lam e =>
    apply semantics_preservation.lift_lam
    apply Hτ₀; apply Hτ₁
  case fix₁ fᵥ HvalueFix =>
    apply semantics_preservation.fix₁
    apply HvalueFix; apply Hτ₀; apply Hτ₁
  case ifz₁_then =>
    apply semantics_preservation.ifz₁_then
    apply Hτ₀; apply Hτ₁
  case ifz₁_else =>
    apply semantics_preservation.ifz₁_else
    apply Hτ₀; apply Hτ₁
  all_goals
    constructor
    -- left approximation
    . apply log_approx.fundamental
      apply typing.erase.safety
      apply Hτ₀
    -- right approximation
    . apply log_approx.fundamental
      apply typing.erase.safety
      apply Hτ₁
