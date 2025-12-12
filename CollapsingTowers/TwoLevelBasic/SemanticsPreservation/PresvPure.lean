import CollapsingTowers.TwoLevelBasic.LogicalEquiv.Defs

-- value v
-- —————————————
-- value γ₀(‖v‖)
--
--
-- value n  value λ.e        value (code x)  value (code e)
-- ———————  ———————————————  ——————————————  ——————————————————
-- value n  value λ.γ₀(‖e‖)  value γ₀(x)     Binding Time Error
lemma semantics_preservation.erase_value :
  ∀ Γ v τ φ γ₀ γ₁,
    value v →
    wbt 𝟙 τ →
    typing Γ 𝟙 v τ φ →
    log_equiv_env γ₀ γ₁ (erase_env Γ) →
    value (msubst γ₀ ‖v‖) ∧ value (msubst γ₁ ‖v‖) :=
  by
  intros Γ v τ φ γ₀ γ₁ Hvalue HwellBinds Hτ HsemΓ
  have ⟨Hmwf₀, Hmwf₁⟩ := log_equiv_env.mwf _ _ _ HsemΓ
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
    apply log_equiv_value.syntactic.value
    apply log_equiv_env.binds_log_equiv_value
    apply HsemΓ; apply erase_env.binds; assumption

lemma semantics_preservation.lets :
  ∀ Γ e bᵥ τ φ₀ φ₁,
    value bᵥ →
    typing Γ 𝟙 (.lets bᵥ e) τ φ₀ →
    typing Γ 𝟙 (opening 0 bᵥ e) τ φ₁ →
    log_equiv (erase_env Γ) ‖.lets bᵥ e‖ ‖opening 0 bᵥ e‖ (erase_ty τ) :=
  by
  intros Γ e bᵥ τ φ₀ φ₁ HvalueBind Hτ₀ Hτ₁
  have HEτ₀ := typing.erase.safety _ _ _ _ _ Hτ₀
  have HEτ₁ := typing.erase.safety _ _ _ _ _ Hτ₁
  constructor; apply HEτ₀
  constructor; apply HEτ₁
  intros γ₀ γ₁ HsemΓ
  have ⟨Hmwf₀, Hmwf₁⟩ := log_equiv_env.mwf _ _ _ HsemΓ
  have ⟨HSτ₀, HSτ₁⟩ := log_equiv_env.msubst.typing _ _ _ _ _ _ HEτ₀ HEτ₁ HsemΓ
  simp at HSτ₀ HSτ₁
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
  have ⟨_, _, IH⟩ := log_equiv.fundamental _ _ _ HEτ₁
  simp only [log_equiv_expr] at IH
  have ⟨v₀, v₁, Hstep₀, Hstep₁, Hsem_value⟩ := IH _ _ HsemΓ
  have HEq : opening 0 (msubst γ₀ ‖bᵥ‖) (msubst γ₀ ‖e‖) = msubst γ₀ ‖opening 0 bᵥ e‖ :=
    by rw [comm.erase_opening_value, comm.msubst_opening_value]; apply Hmwf₀
  rw [← HEq] at Hstep₀
  --
  --
  simp only [log_equiv_expr]
  exists v₀, v₁
  constructor
  . simp
    apply stepn.multi _ _ _ _ Hstep₀
    apply step_lvl.pure _ _ _ ctx𝕄.hole
    . apply typing.regular _ _ _ _ _ HSτ₀
    . apply head.lets; apply HvalueBind₀
  constructor
  . apply Hstep₁
  . apply Hsem_value

lemma semantics_preservation.app₁ :
  ∀ Γ e argᵥ τ φ₀ φ₁,
    value argᵥ →
    typing Γ 𝟙 (.app₁ (.lam e) argᵥ) τ φ₀ →
    typing Γ 𝟙 (opening 0 argᵥ e) τ φ₁ →
    log_equiv (erase_env Γ) ‖.app₁ (.lam e) argᵥ‖ ‖opening 0 argᵥ e‖ (erase_ty τ) :=
  by
  intros Γ e argᵥ τ φ₀ φ₁ HvalueArg Hτ₀ Hτ₁
  have HEτ₀ := typing.erase.safety _ _ _ _ _ Hτ₀
  have HEτ₁ := typing.erase.safety _ _ _ _ _ Hτ₁
  constructor; apply HEτ₀
  constructor; apply HEτ₁
  intros γ₀ γ₁ HsemΓ
  have ⟨Hmwf₀, Hmwf₁⟩ := log_equiv_env.mwf _ _ _ HsemΓ
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
  have ⟨_, _, IH⟩ := log_equiv.fundamental _ _ _ HEτ₁
  simp only [log_equiv_expr] at IH
  have ⟨v₀, v₁, Hstep₀, Hstep₁, Hsem_value⟩ := IH _ _ HsemΓ
  have HEq : opening 0 (msubst γ₀ ‖argᵥ‖) (msubst γ₀ ‖e‖) = msubst γ₀ ‖opening 0 argᵥ e‖ :=
    by rw [comm.erase_opening_value, comm.msubst_opening_value]; apply Hmwf₀
  rw [← HEq] at Hstep₀
  --
  --
  simp only [log_equiv_expr]
  exists v₀, v₁
  constructor
  . simp
    apply stepn.multi _ _ _ _ Hstep₀
    apply step_lvl.pure _ _ _ ctx𝕄.hole
    . constructor; apply lc.value _ HvalueFun₀; apply lc.value _ HvalueArg₀
    . apply head.app₁; apply HvalueArg₀
  constructor
  . apply Hstep₁
  . apply Hsem_value

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
  apply log_equiv.fundamental; apply typing.erase.safety; apply Hτ₀

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
  case lift_lam e =>
    apply semantics_preservation.lift_lam
    apply Hτ₀; apply Hτ₁
  all_goals
    apply log_equiv.fundamental
    apply typing.erase.safety
    apply Hτ₀
