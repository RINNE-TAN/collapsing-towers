import Instar.TwoLevelMut.LogicalEquiv.Defs

-- value v
-- —————————————
-- value γ₀(‖v‖)
--
--
-- value n  value λ.e        value (code x)  value (code e)
-- ———————  ———————————————  ——————————————  ——————————————————
-- value n  value λ.γ₀(‖e‖)  value γ₀(x)     Binding Time Error
lemma semantics_preservation.erase_value :
  ∀ Γ v τ ε 𝓦 γ₀ γ₁,
    value v →
    wbt 𝟙 τ →
    typing Γ 𝟙 v τ ε →
    log_equiv_env 𝓦 γ₀ γ₁ (erase_env Γ) →
    value (msubst γ₀ ‖v‖) ∧ value (msubst γ₁ ‖v‖) :=
  by
  intros Γ v τ ε 𝓦 γ₀ γ₁ Hvalue HwellBinds Hτ HsemΓ
  have ⟨Hmwf₀, Hmwf₁⟩ := log_equiv_env.syntactic.mwf _ _ _ _ HsemΓ
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
  case unit =>
    simp; apply value.unit
  case loc =>
    simp; apply value.loc

lemma semantics_preservation.lets :
  ∀ Γ e bᵥ τ ε₀ ε₁,
    value bᵥ →
    typing Γ 𝟙 (.lets bᵥ e) τ ε₀ →
    typing Γ 𝟙 (opening 0 bᵥ e) τ ε₁ →
    log_equiv (erase_env Γ) ‖.lets bᵥ e‖ ‖opening 0 bᵥ e‖ (erase_ty τ) :=
  by
  intros Γ e bᵥ τ ε₀ ε₁ HvalueBind Hτ₀ Hτ₁
  have HEτ₀ := typing.erase.safety _ _ _ _ _ Hτ₀
  have HEτ₁ := typing.erase.safety _ _ _ _ _ Hτ₁
  constructor; apply HEτ₀
  constructor; apply HEτ₁
  intros 𝓦₀ γ₀ γ₁ HsemΓ
  have ⟨Hmwf₀, Hmwf₁⟩ := log_equiv_env.syntactic.mwf _ _ _ _ HsemΓ
  simp only [log_equiv_expr]
  intros σ₀ σ₁ Hsem_store
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
  have ⟨𝓦₁, σ₂, σ₃, v₀, v₁, Hfuture₀, Hstep₀, Hstep₁, Hsem_store, Hsem_value⟩ := IH _ _ _ HsemΓ _ _ Hsem_store
  have HEq : opening 0 (msubst γ₀ ‖bᵥ‖) (msubst γ₀ ‖e‖) = msubst γ₀ ‖opening 0 bᵥ e‖ :=
    by rw [comm.erase_opening_value, comm.msubst_opening_value]; apply Hmwf₀
  rw [← HEq] at Hstep₀
  --
  --
  exists 𝓦₁, σ₂, σ₃, v₀, v₁
  constructor
  . apply Hfuture₀
  constructor
  . apply stepn.multi _ _ _ _ Hstep₀
    apply step_lvl.pure _ _ _ _ ctx𝕄.hole
    . apply lc.under_msubst _ _ _ Hmwf₀ (typing.regular _ _ _ _ _ HEτ₀)
    . simp; apply head_pure.lets; apply HvalueBind₀
  constructor
  . apply Hstep₁
  constructor
  . apply Hsem_store
  . apply Hsem_value

lemma semantics_preservation.app₁ :
  ∀ Γ e argᵥ τ ε₀ ε₁,
    value argᵥ →
    typing Γ 𝟙 (.app₁ (.lam e) argᵥ) τ ε₀ →
    typing Γ 𝟙 (opening 0 argᵥ e) τ ε₁ →
    log_equiv (erase_env Γ) ‖.app₁ (.lam e) argᵥ‖ ‖opening 0 argᵥ e‖ (erase_ty τ) :=
  by
  intros Γ e argᵥ τ ε₀ ε₁ HvalueArg Hτ₀ Hτ₁
  have HEτ₀ := typing.erase.safety _ _ _ _ _ Hτ₀
  have HEτ₁ := typing.erase.safety _ _ _ _ _ Hτ₁
  constructor; apply HEτ₀
  constructor; apply HEτ₁
  intros 𝓦₀ γ₀ γ₁ HsemΓ
  have ⟨Hmwf₀, Hmwf₁⟩ := log_equiv_env.syntactic.mwf _ _ _ _ HsemΓ
  simp only [log_equiv_expr]
  intros σ₀ σ₁ Hsem_store
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
  have ⟨𝓦₁, σ₂, σ₃, v₀, v₁, Hfuture₀, Hstep₀, Hstep₁, Hsem_store, Hsem_value⟩ := IH _ _ _ HsemΓ _ _ Hsem_store
  have HEq : opening 0 (msubst γ₀ ‖argᵥ‖) (msubst γ₀ ‖e‖) = msubst γ₀ ‖opening 0 argᵥ e‖ :=
    by rw [comm.erase_opening_value, comm.msubst_opening_value]; apply Hmwf₀
  rw [← HEq] at Hstep₀
  --
  --
  exists 𝓦₁, σ₂, σ₃, v₀, v₁
  constructor
  . apply Hfuture₀
  constructor
  . apply stepn.multi _ _ _ _ Hstep₀
    apply step_lvl.pure _ _ _ _ ctx𝕄.hole
    . apply lc.under_msubst _ _ _ Hmwf₀ (typing.regular _ _ _ _ _ HEτ₀)
    . simp; apply head_pure.app₁; apply HvalueArg₀
  constructor
  . apply Hstep₁
  constructor
  . apply Hsem_store
  . apply Hsem_value

lemma semantics_preservation.lift_lam :
  ∀ Γ e τ ε₀ ε₁,
    typing Γ 𝟙 (.lift (.lam e)) τ ε₀ →
    typing Γ 𝟙 (.lam𝕔 (codify 0 e)) τ ε₁ →
    log_equiv (erase_env Γ) ‖.lift (.lam e)‖ ‖.lam𝕔 (codify 0 e)‖ (erase_ty τ) :=
  by
  intros Γ e τ ε₀ ε₁ Hτ₀ Hτ₁
  have HEq : ‖.lam𝕔 (codify 0 e)‖ = ‖.lift (.lam e)‖ :=
    by simp [identity.erase_codify]
  rw [HEq]
  apply log_equiv.fundamental; apply typing.erase.safety; apply Hτ₀

theorem semantics_preservation.pure.head :
  ∀ Γ e₀ e₁ τ ε,
    e₀ ↝ e₁ →
    typing Γ 𝟙 e₀ τ ε →
    log_equiv (erase_env Γ) ‖e₀‖ ‖e₁‖ (erase_ty τ) :=
  by
  intros Γ e₀ e₁ τ ε Hhead Hτ₀
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
