import Instar.TwoLevelFinal.LogicalEquiv.Defs

-- value v
-- —————————————
-- value γ₀(‖v‖)
--
--
-- value n  value λ.e        value (code x)  value (code e)
-- ———————  ———————————————  ——————————————  ——————————————————
-- value n  value λ.γ₀(‖e‖)  value γ₀(x)     Binding Time Error
lemma semantics_preservation.erase_value :
  ∀ k 𝓦 Γ v τ φ γ₀ γ₁,
    value v →
    wbt 𝟙 τ →
    typing Γ 𝟙 v τ φ →
    log_approx_env (k, 𝓦) γ₀ γ₁ (erase_env Γ) →
    value (msubst γ₀ ‖v‖) ∧ value (msubst γ₁ ‖v‖) :=
  by
  intros k 𝓦 Γ v τ φ γ₀ γ₁ Hvalue HwellBinds Hτ HsemΓ
  have ⟨Hmwf₀, Hmwf₁⟩ := log_approx_env.syntactic.mwf _ _ _ _ _ HsemΓ
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
  case unit =>
    simp; apply value.unit
  case loc => contradiction

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
    intros k 𝓦₀ γ₀ γ₁ HsemΓ
    have ⟨Hmwf₀, Hmwf₁⟩ := log_approx_env.syntactic.mwf _ _ _ _ _ HsemΓ
    have ⟨HmG₀, HmG₁⟩ := log_approx_env.syntactic.mgrounded _ _ _ _ _ HsemΓ
    have HG₀ : grounded (msubst γ₀ ‖.lets bᵥ e‖) :=
      by
      apply grounded.under_msubst _ _ HmG₀
      apply typing.dynamic_impl_grounded _ _ _ _ HEτ₀
    have HG₁ : grounded (msubst γ₁ ‖opening 0 bᵥ e‖) :=
      by
      apply grounded.under_msubst _ _ HmG₁
      apply typing.dynamic_impl_grounded _ _ _ _ HEτ₁
    simp at HG₀ HG₁
    simp only [log_approx_expr]
    intros j Hindexj σ₀ σ₁ Hsem_store σ₂ v₀ Hvalue₀ Hstep₀
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
    simp at Hstep₀
    --
    --
    -- ⟨σ₀, lets x = γ₀‖bᵥ‖ in γ₀‖e‖⟩ ⭢ ⟦j⟧ ⟨σ₂, v₀⟩
    -- ——————————————————————————————————————————————
    -- i + 1 = j
    -- ⟨σ₀, (x ↦ γ₀‖bᵥ‖, γ₀)‖e‖⟩ ⭢ ⟦i⟧ ⟨σ₂, v₀⟩
    have ⟨_, z, i, _, HEqj, _, Hstepr, Hstep₀⟩ :=
      stepn_indexed.refine.lets _ _ _ _ _ _ Hvalue₀ HG₀ Hstep₀
    have ⟨HEqσ, HEqv, Hz⟩ := stepn_indexed.value_impl_termination _ _ _ _ _ HvalueBind₀ Hstepr
    rw [← HEqσ, ← HEqv] at Hstep₀
    --
    --
    -- ⟨σ₀, (x ↦ γ₀‖bᵥ‖, γ₀)‖e‖⟩ ⭢ ⟦i⟧ ⟨σ₂, v₀⟩
    -- —————————————————————————————————————————
    -- ⟨σ₀, γ₀‖(x ↦ bᵥ)e‖⟩ ⭢ ⟦i⟧ ⟨σ₂, v₀⟩
    have HEq : opening 0 (msubst γ₀ ‖bᵥ‖) (msubst γ₀ ‖e‖) = msubst γ₀ ‖opening 0 bᵥ e‖ :=
      by rw [comm.erase_opening_value, comm.msubst_opening_value]; apply Hmwf₀
    rw [HEq] at Hstep₀
    --
    --
    -- ⟨σ₀, γ₀‖(x ↦ bᵥ)e‖⟩ ⭢ ⟦i⟧ ⟨σ₂, v₀⟩
    -- ‖Γ‖ ⊧ ‖(x ↦ bᵥ)e‖ ≤𝑙𝑜𝑔 ‖(x ↦ bᵥ)e‖ : ‖τ‖
    -- —————————————————————————————————————————
    -- ⟨σ₁, γ₁‖(x ↦ bᵥ)e‖⟩ ⭢* ⟨σ₃, v₁⟩
    -- (σ₂, σ₃) : 𝓦₁
    -- (k - i, 𝓦₁, v₀, v₁) ∈ 𝓥⟦‖τ‖⟧
    have ⟨_, _, IH⟩ := log_approx.fundamental _ _ _ HEτ₁
    simp only [log_approx_expr] at IH
    have ⟨𝓦₁, σ₃, v₁, Hfuture₀, Hstep₁, Hsem_store, Hsem_value⟩ := IH _ _ _ _ HsemΓ i (by omega) _ _ Hsem_store _ _ Hvalue₀ Hstep₀
    have ⟨_, Hfuture₀⟩ := Hfuture₀
    exists 𝓦₁, σ₃, v₁
    constructor
    . constructor; omega; apply Hfuture₀
    constructor
    . apply Hstep₁
    constructor
    . apply Hsem_store
    . apply log_approx_value.antimono
      apply Hsem_value; simp; omega
  -- right approximation
  . have HEτ₀ := typing.erase.safety _ _ _ _ _ Hτ₁
    have HEτ₁ := typing.erase.safety _ _ _ _ _ Hτ₀
    constructor; apply HEτ₀
    constructor; apply HEτ₁
    intros k 𝓦₀ γ₀ γ₁ HsemΓ
    have ⟨Hmwf₀, Hmwf₁⟩ := log_approx_env.syntactic.mwf _ _ _ _ _ HsemΓ
    have ⟨HmG₀, HmG₁⟩ := log_approx_env.syntactic.mgrounded _ _ _ _ _ HsemΓ
    have HG₀ : grounded (msubst γ₀ ‖opening 0 bᵥ e‖) :=
      by
      apply grounded.under_msubst _ _ HmG₀
      apply typing.dynamic_impl_grounded _ _ _ _ HEτ₀
    have HG₁ : grounded (msubst γ₁ ‖.lets bᵥ e‖) :=
      by
      apply grounded.under_msubst _ _ HmG₁
      apply typing.dynamic_impl_grounded _ _ _ _ HEτ₁
    simp at HG₀ HG₁
    simp only [log_approx_expr]
    intros j Hindexj σ₀ σ₁ Hsem_store σ₂ v₀ Hvalue₀ Hstep₀
    --
    --
    -- ⟨σ₀, γ₀‖(x ↦ bᵥ)e‖⟩ ⭢ ⟦j⟧ ⟨σ₂, v₀⟩
    -- ‖Γ‖ ⊧ ‖(x ↦ bᵥ)e‖ ≤𝑙𝑜𝑔 ‖(x ↦ bᵥ)e‖ : ‖τ‖
    -- —————————————————————————————————————————
    -- ⟨σ₁, γ₁‖(x ↦ bᵥ)e‖⟩ ⭢* ⟨σ₃, v₁⟩
    -- (σ₂, σ₃) : 𝓦₁
    -- (k - j, 𝓦₁, v₀, v₁) ∈ 𝓥⟦‖τ‖⟧
    have ⟨_, _, IH⟩ := log_approx.fundamental _ _ _ HEτ₀
    simp only [log_approx_expr] at IH
    have ⟨𝓦₁, σ₃, v₁, Hfuture₀, Hstep₁, Hsem_store, Hsem_value⟩ := IH _ _ _ _ HsemΓ j (by omega) _ _ Hsem_store _ _ Hvalue₀ Hstep₀
    have ⟨_, Hfuture₀⟩ := Hfuture₀
    --
    --
    -- ⟨σ₁, (x ↦ γ₁‖bᵥ‖, γ₁)‖e‖⟩ ⭢* ⟨σ₃, v₁⟩
    -- ——————————————————————————————————————
    -- ⟨σ₁, γ₁‖(x ↦ bᵥ)e‖⟩ ⭢* ⟨σ₃, v₁⟩
    have HEq : msubst γ₁ ‖opening 0 bᵥ e‖ = opening 0 (msubst γ₁ ‖bᵥ‖) (msubst γ₁ ‖e‖) :=
      by rw [comm.erase_opening_value, comm.msubst_opening_value]; apply Hmwf₁
    rw [HEq] at Hstep₁
    --
    --
    -- ⟨σ₁, γ₁‖(x ↦ bᵥ)e‖⟩ ⭢* ⟨σ₃, v₁⟩
    -- ———————————————————————————————————————————
    -- ⟨σ₁, lets x = γ₁‖bᵥ‖ in γ₁‖e‖⟩ ⭢* ⟨σ₃, v₁⟩
    exists 𝓦₁, σ₃, v₁
    constructor
    . constructor; omega; apply Hfuture₀
    constructor
    . simp
      apply stepn.multi _ _ _ _ Hstep₁
      apply step_lvl.pure _ _ _ _ ctx𝕄.hole
      . rw [← msubst.lets]
        apply lc.under_msubst _ _ _ Hmwf₁
        apply typing.regular _ _ _ _ _ HEτ₁
      . apply head_pure.lets
        have ⟨HvalueBind₀, HvalueBind₁⟩ : value (msubst γ₀ ‖bᵥ‖) ∧ value (msubst γ₁ ‖bᵥ‖) :=
          by
          cases Hτ₀
          case lets Hwbt Hτb Hclosed Hτe =>
            apply semantics_preservation.erase_value
            apply HvalueBind; apply Hwbt; apply Hτb; apply HsemΓ
        apply HvalueBind₁
    constructor
    . apply Hsem_store
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
    intros k 𝓦₀ γ₀ γ₁ HsemΓ
    have ⟨Hmwf₀, Hmwf₁⟩ := log_approx_env.syntactic.mwf _ _ _ _ _ HsemΓ
    have ⟨HmG₀, HmG₁⟩ := log_approx_env.syntactic.mgrounded _ _ _ _ _ HsemΓ
    have HG₀ : grounded (msubst γ₀ ‖.app₁ (.lam e) argᵥ‖) :=
      by
      apply grounded.under_msubst _ _ HmG₀
      apply typing.dynamic_impl_grounded _ _ _ _ HEτ₀
    have HG₁ : grounded (msubst γ₁ ‖opening 0 argᵥ e‖) :=
      by
      apply grounded.under_msubst _ _ HmG₁
      apply typing.dynamic_impl_grounded _ _ _ _ HEτ₁
    simp at HG₀ HG₁
    simp only [log_approx_expr]
    intros j Hindexj σ₀ σ₁ Hsem_store σ₂ v₀ Hvalue₀ Hstep₀
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
    -- ⟨σ₀, λx.γ₀‖e₀‖ @ γ₀‖argᵥ‖⟩ ⭢ ⟦j⟧ ⟨σ₂, v₀⟩
    -- ——————————————————————————————————————————————
    -- i + 1 = j
    -- ⟨σ₀, (x ↦ γ₀‖argᵥ‖, γ₀)‖e‖⟩ ⭢ ⟦i⟧ ⟨σ₂, v₀⟩
    simp at Hstep₀
    have ⟨i, HEqj, Hstep₀⟩ := stepn_indexed.refine.app₁.eliminator _ _ _ _ _ _ HvalueFun₀ HvalueArg₀ Hvalue₀ Hstep₀
    --
    --
    -- ⟨σ₀, λx.γ₀‖e₀‖ @ γ₀‖argᵥ‖⟩ ⭢ ⟦j⟧ ⟨σ₂, v₀⟩
    -- —————————————————————————————————————————
    -- ⟨σ₀, γ₀‖(x ↦ argᵥ)e‖⟩ ⭢ ⟦i⟧ ⟨σ₂, v₀⟩
    have HEq : opening 0 (msubst γ₀ ‖argᵥ‖) (msubst γ₀ ‖e‖) = msubst γ₀ ‖opening 0 argᵥ e‖ :=
      by rw [comm.erase_opening_value, comm.msubst_opening_value]; apply Hmwf₀
    rw [HEq] at Hstep₀
    --
    --
    -- ⟨σ₀, γ₀‖(x ↦ argᵥ)e‖⟩ ⭢ ⟦i⟧ ⟨σ₂, v₀⟩
    -- ‖Γ‖ ⊧ ‖(x ↦ argᵥ)e‖ ≤𝑙𝑜𝑔 ‖(x ↦ argᵥ)e‖ : ‖τ‖
    -- ————————————————————————————————————————————
    -- ⟨σ₁, γ₁‖(x ↦ argᵥ)e‖⟩ ⭢* ⟨σ₃, v₁⟩
    -- (σ₂, σ₃) : 𝓦₁
    -- (k - i, 𝓦₁, v₀, v₁) ∈ 𝓥⟦‖τ‖⟧
    have ⟨_, _, IH⟩ := log_approx.fundamental _ _ _ HEτ₁
    simp only [log_approx_expr] at IH
    have ⟨𝓦₁, σ₃, v₁, Hfuture₀, Hstep₁, Hsem_store, Hsem_value⟩ := IH _ _ _ _ HsemΓ i (by omega) _ _ Hsem_store _ _ Hvalue₀ Hstep₀
    have ⟨_, Hfuture₀⟩ := Hfuture₀
    exists 𝓦₁, σ₃, v₁
    constructor
    . constructor; omega; apply Hfuture₀
    constructor
    . apply Hstep₁
    constructor
    . apply Hsem_store
    . apply log_approx_value.antimono
      apply Hsem_value; simp; omega
  -- right approximation
  . have HEτ₀ := typing.erase.safety _ _ _ _ _ Hτ₁
    have HEτ₁ := typing.erase.safety _ _ _ _ _ Hτ₀
    constructor; apply HEτ₀
    constructor; apply HEτ₁
    intros k 𝓦₀ γ₀ γ₁ HsemΓ
    have ⟨Hmwf₀, Hmwf₁⟩ := log_approx_env.syntactic.mwf _ _ _ _ _ HsemΓ
    have ⟨HmG₀, HmG₁⟩ := log_approx_env.syntactic.mgrounded _ _ _ _ _ HsemΓ
    have HG₀ : grounded (msubst γ₀ ‖opening 0 argᵥ e‖) :=
      by
      apply grounded.under_msubst _ _ HmG₀
      apply typing.dynamic_impl_grounded _ _ _ _ HEτ₀
    have HG₁ : grounded (msubst γ₁ ‖.app₁ (.lam e) argᵥ‖) :=
      by
      apply grounded.under_msubst _ _ HmG₁
      apply typing.dynamic_impl_grounded _ _ _ _ HEτ₁
    simp at HG₀ HG₁
    simp only [log_approx_expr]
    intros j Hindexj σ₀ σ₁ Hsem_store σ₂ v₀ Hvalue₀ Hstep₀
    --
    --
    -- ⟨σ₀, γ₀‖(x ↦ argᵥ)e‖⟩ ⭢ ⟦j⟧ ⟨σ₂, v₀⟩
    -- ‖Γ‖ ⊧ ‖(x ↦ argᵥ)e‖ ≤𝑙𝑜𝑔 ‖(x ↦ argᵥ)e‖ : ‖τ‖
    -- ————————————————————————————————————————————
    -- ⟨σ₁, γ₁‖(x ↦ argᵥ)e‖⟩ ⭢* ⟨σ₃, v₁⟩
    -- (σ₂, σ₃) : 𝓦₁
    -- (k - j, 𝓦₁, v₀, v₁) ∈ 𝓥⟦‖τ‖⟧
    have ⟨_, _, IH⟩ := log_approx.fundamental _ _ _ HEτ₀
    simp only [log_approx_expr] at IH
    have ⟨𝓦₁, σ₃, v₁, Hfuture₀, Hstep₁, Hsem_store, Hsem_value⟩ := IH _ _ _ _ HsemΓ j (by omega) _ _ Hsem_store _ _ Hvalue₀ Hstep₀
    have ⟨_, Hfuture₀⟩ := Hfuture₀
    --
    --
    -- ⟨σ₁, γ₁‖(x ↦ argᵥ)e‖⟩ ⭢* ⟨σ₃, v₁⟩
    -- ————————————————————————————————————————
    -- ⟨σ₁, (x ↦ γ₁‖argᵥ‖, γ₁)‖e‖⟩ ⭢* ⟨σ₃, v₁⟩
    have HEq : msubst γ₁ ‖opening 0 argᵥ e‖ = opening 0 (msubst γ₁ ‖argᵥ‖) (msubst γ₁ ‖e‖) :=
      by rw [comm.erase_opening_value, comm.msubst_opening_value]; apply Hmwf₁
    rw [HEq] at Hstep₁
    --
    --
    -- ⟨σ₁, (x ↦ γ₁‖argᵥ‖, γ₁)‖e‖⟩ ⭢* ⟨σ₃, v₁⟩
    -- —————————————————————————————————————————
    -- ⟨σ₁, (λx.γ₁‖e‖) @ γ₁‖argᵥ‖⟩ ⭢* ⟨σ₃, v₁⟩
    exists 𝓦₁, σ₃, v₁
    constructor
    . constructor; omega; apply Hfuture₀
    constructor
    . simp
      apply stepn.multi _ _ _ _ Hstep₁
      apply step_lvl.pure _ _ _ _ ctx𝕄.hole
      . rw [← msubst.lam, ← msubst.app₁]
        apply lc.under_msubst _ _ _ Hmwf₁
        apply typing.regular _ _ _ _ _ HEτ₁
      . apply head_pure.app₁
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
    constructor
    . apply Hsem_store
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
    intros k 𝓦₀ γ₀ γ₁ HsemΓ
    simp only [log_approx_expr]
    intros j Hindexj σ₀ σ₁ Hsem_store σ₂ v₀ Hvalue₀ Hstep₀
    simp at Hstep₀
    have ⟨HEqσ, _, HEqv⟩ := stepn_indexed.refine.binary₁.eliminator _ _ _ _ _ _ _ Hvalue₀ Hstep₀
    rw [← HEqσ, HEqv]
    exists 𝓦₀, σ₁, .lit (eval op l r)
    constructor
    . constructor; omega; simp
    constructor
    . simp [- eval]; apply stepn.refl
    constructor
    . apply Hsem_store
    . simp
  -- right approximation
  . have HEτ₀ := typing.erase.safety _ _ _ _ _ Hτ₁
    have HEτ₁ := typing.erase.safety _ _ _ _ _ Hτ₀
    constructor; apply HEτ₀
    constructor; apply HEτ₁
    intros k 𝓦₀ γ₀ γ₁ HsemΓ
    simp only [log_approx_expr]
    intros j Hindexj σ₀ σ₁ Hsem_store σ₂ v₀ Hvalue₀ Hstep₀
    simp [- eval] at Hstep₀
    have ⟨HEqσ, HEqv, _⟩ := stepn_indexed.value_impl_termination _ _ _ _ _ (value.lit _) Hstep₀
    rw [← HEqσ, ← HEqv]
    exists 𝓦₀, σ₁, .lit (eval op l r)
    constructor
    . constructor; omega; simp
    constructor
    . apply stepn.multi _ _ _ _ (stepn.refl _)
      apply step_lvl.pure _ _ _ _ ctx𝕄.hole
      . simp
      . simp [- eval]; apply head_pure.binary₁
    constructor
    . apply Hsem_store
    . simp

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
    intros k 𝓦₀ γ₀ γ₁ HsemΓ
    have ⟨Hmwf₀, Hmwf₁⟩ := log_approx_env.syntactic.mwf _ _ _ _ _ HsemΓ
    have ⟨HmG₀, HmG₁⟩ := log_approx_env.syntactic.mgrounded _ _ _ _ _ HsemΓ
    have HG₀ : grounded (msubst γ₀ ‖.fix₁ fᵥ‖) :=
      by
      apply grounded.under_msubst _ _ HmG₀
      apply typing.dynamic_impl_grounded _ _ _ _ HEτ₀
    have HG₁ : grounded (msubst γ₁ ‖.lam (.app₁ (.app₁ fᵥ (.fix₁ fᵥ)) (.bvar 0))‖) :=
      by
      apply grounded.under_msubst _ _ HmG₁
      apply typing.dynamic_impl_grounded _ _ _ _ HEτ₁
    simp at HG₀ HG₁
    simp only [log_approx_expr]
    intros j Hindexj σ₀ σ₁ Hsem_store σ₂ v₀ Hvalue₀ Hstep₀
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
    -- ⟨σ₀, fix γ₀‖fᵥ‖⟩ ⭢ ⟦j⟧ ⟨σ₂, v₀⟩
    -- ———————————————————————————————
    -- σ₀ = σ₂
    -- v₀ = γ₀‖λx.fᵥ @ (fix fᵥ) @ x‖
    simp at Hstep₀
    have ⟨z, r, _, _, Hstepr, HEqv⟩ :=
      stepn_indexed.refine.fix₁.constructor _ _ _ _ _ Hvalue₀ HG₀ Hstep₀
    have ⟨HEqσ, HEqr, Hz⟩ := stepn_indexed.value_impl_termination _ _ _ _ _ HvalueFix₀ Hstepr
    rw [← HEqσ, HEqv, ← HEqr]
    --
    --
    -- ‖Γ‖ ⊧ ‖λx.fᵥ @ (fix fᵥ) @ x‖ ≤𝑙𝑜𝑔 ‖λx.fᵥ @ (fix fᵥ) @ x‖ : ‖τ‖
    -- —————————————————————————————————————————————————————————————————————
    -- (k, 𝓦₁, γ₀‖λx.fᵥ @ (fix fᵥ) @ x‖, γ₁‖λx.fᵥ @ (fix fᵥ) @ x‖) ∈ 𝓥⟦‖τ‖⟧
    have ⟨_, _, IH⟩ := log_approx.fundamental _ _ _ HEτ₁
    simp only [log_approx_expr] at IH
    have ⟨𝓦₁, σ₃, v₁, Hfuture₀, Hstep₁, Hsem_store, Hsem_value⟩ := IH _ _ _ _ HsemΓ 0 (by omega) _ _ Hsem_store _ _ HvalueFun₀ (stepn_indexed.refl _)
    have ⟨_, Hfuture₀⟩ := Hfuture₀
    exists 𝓦₁, σ₃, v₁
    constructor
    . simp; apply Hfuture₀
    constructor
    . apply Hstep₁
    constructor
    . apply Hsem_store
    . simp at Hsem_value
      apply log_approx_value.antimono
      apply Hsem_value; simp
  -- right approximation
  . have HEτ₀ := typing.erase.safety _ _ _ _ _ Hτ₁
    have HEτ₁ := typing.erase.safety _ _ _ _ _ Hτ₀
    constructor; apply HEτ₀
    constructor; apply HEτ₁
    intros k 𝓦₀ γ₀ γ₁ HsemΓ
    have ⟨Hmwf₀, Hmwf₁⟩ := log_approx_env.syntactic.mwf _ _ _ _ _ HsemΓ
    simp only [log_approx_expr]
    intros j Hindexj σ₀ σ₁ Hsem_store σ₂ v₀ Hvalue₀ Hstep₀
    --
    --
    -- ⟨σ₀, γ₀‖λx.fᵥ @ (fix fᵥ) @ x‖⟩ ⭢ ⟦j⟧ ⟨σ₂, v₀⟩
    -- ‖Γ‖ ⊧ ‖λx.fᵥ @ (fix fᵥ) @ x‖ ≤𝑙𝑜𝑔 ‖λx.fᵥ @ (fix fᵥ) @ x‖ : ‖τ‖
    -- —————————————————————————————————————————————————————————————
    -- ⟨σ₁, γ₁‖λx.fᵥ @ (fix fᵥ) @ x‖⟩ ⭢* ⟨σ₃, v₁⟩
    -- (σ₂, σ₃) : 𝓦₁
    -- (k - j, 𝓦₁, v₀, v₁) ∈ 𝓥⟦‖τ‖⟧
    have ⟨_, _, IH⟩ := log_approx.fundamental _ _ _ HEτ₀
    simp only [log_approx_expr] at IH
    have ⟨𝓦₁, σ₃, v₁, Hfuture₀, Hstep₁, Hsem_store, Hsem_value⟩ := IH _ _ _ _ HsemΓ j (by omega) _ _ Hsem_store _ _ Hvalue₀ Hstep₀
    have ⟨_, Hfuture₀⟩ := Hfuture₀
    simp at Hstep₁
    --
    --
    -- ⟨σ₁, γ₁‖λx.fᵥ @ (fix fᵥ) @ x‖⟩ ⭢* ⟨σ₃, v₁⟩
    -- ———————————————————————————————————————————
    -- ⟨σ₁, γ₁‖fix fᵥ‖⟩ ⭢* ⟨σ₃, v₁⟩
    exists 𝓦₁, σ₃, v₁
    constructor
    . simp; apply Hfuture₀
    constructor
    . simp
      apply stepn.multi _ _ _ _ Hstep₁
      apply step_lvl.pure _ _ _ _ ctx𝕄.hole
      . rw [← msubst.fix₁]
        apply lc.under_msubst _ _ _ Hmwf₁
        apply typing.regular _ _ _ _ _ HEτ₁
      . apply head_pure.fix₁
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
    constructor
    . apply Hsem_store
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
    intros k 𝓦₀ γ₀ γ₁ HsemΓ
    simp only [log_approx_expr]
    intros j Hindexj σ₀ σ₁ Hsem_store σ₂ v₀ Hvalue₀ Hstep₀
    --
    --
    -- ⟨σ₀, if 0 then γ₀‖l‖ else γ₀‖r‖⟩ ⭢ ⟦j⟧ ⟨σ₂, v₀⟩
    -- ————————————————————————————————————————————————
    -- i + 1 = j
    -- ⟨σ₀, γ₀‖l‖⟩ ⭢* ⟦i⟧ ⟨σ₂, v₀⟩
    simp at Hstep₀
    have ⟨i, HEqj, Hstep₀⟩ := stepn_indexed.refine.ifz₁_then.eliminator _ _ _ _ _ _ Hvalue₀ Hstep₀
    --
    --
    -- ⟨σ₀, γ₀‖l‖⟩ ⭢* ⟦i⟧ ⟨σ₂, v₀⟩
    -- ‖Γ‖ ⊧ ‖l‖ ≤𝑙𝑜𝑔 ‖l‖ : ‖τ‖
    -- ——————————————————————————————
    -- ⟨σ₁, γ₁‖l‖⟩ ⭢* ⟨σ₃, v₁⟩
    -- (σ₂, σ₃) : 𝓦₁
    -- (k - i, 𝓦₁, v₀, v₁) ∈ 𝓥⟦‖τ‖⟧
    have ⟨_, _, IH⟩ := log_approx.fundamental _ _ _ HEτ₁
    simp only [log_approx_expr] at IH
    have ⟨𝓦₁, σ₃, v₁, Hfuture₀, Hstep₁, Hsem_store, Hsem_value⟩ := IH _ _ _ _ HsemΓ i (by omega) _ _ Hsem_store _ _ Hvalue₀ Hstep₀
    have ⟨_, Hfuture₀⟩ := Hfuture₀
    exists 𝓦₁, σ₃, v₁
    constructor
    . constructor; omega; apply Hfuture₀
    constructor
    . apply Hstep₁
    constructor
    . apply Hsem_store
    . apply log_approx_value.antimono
      apply Hsem_value; simp; omega
  -- right approximation
  . have HEτ₀ := typing.erase.safety _ _ _ _ _ Hτ₁
    have HEτ₁ := typing.erase.safety _ _ _ _ _ Hτ₀
    constructor; apply HEτ₀
    constructor; apply HEτ₁
    intros k 𝓦₀ γ₀ γ₁ HsemΓ
    have ⟨Hmwf₀, Hmwf₁⟩ := log_approx_env.syntactic.mwf _ _ _ _ _ HsemΓ
    simp only [log_approx_expr]
    intros j Hindexj σ₀ σ₁ Hsem_store σ₂ v₀ Hvalue₀ Hstep₀
    --
    --
    -- ⟨σ₀, γ₀‖l‖⟩ ⭢* ⟦j⟧ ⟨σ₂, v₀⟩
    -- ‖Γ‖ ⊧ ‖l‖ ≤𝑙𝑜𝑔 ‖l‖ : ‖τ‖
    -- ——————————————————————————————
    -- ⟨σ₁, γ₁‖l‖⟩ ⭢* ⟨σ₃, v₁⟩
    -- (σ₂, σ₃) : 𝓦₁
    -- (k - j, 𝓦₁, v₀, v₁) ∈ 𝓥⟦‖τ‖⟧
    have ⟨_, _, IH⟩ := log_approx.fundamental _ _ _ HEτ₀
    simp only [log_approx_expr] at IH
    have ⟨𝓦₁, σ₃, v₁, Hfuture₀, Hstep₁, Hsem_store, Hsem_value⟩ := IH _ _ _ _ HsemΓ j (by omega) _ _ Hsem_store _ _ Hvalue₀ Hstep₀
    have ⟨_, Hfuture₀⟩ := Hfuture₀
    exists 𝓦₁, σ₃, v₁
    constructor
    . constructor; omega; apply Hfuture₀
    constructor
    . apply stepn.multi _ _ _ _ Hstep₁
      apply step_lvl.pure _ _ _ _ ctx𝕄.hole
      . apply lc.under_msubst _ _ _ Hmwf₁
        apply typing.regular _ _ _ _ _ HEτ₁
      . simp; apply head_pure.ifz₁_then
    constructor
    . apply Hsem_store
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
    intros k 𝓦₀ γ₀ γ₁ HsemΓ
    simp only [log_approx_expr]
    intros j Hindexj σ₀ σ₁ Hsem_store σ₂ v₀ Hvalue₀ Hstep₀
    --
    --
    -- ⟨σ₀, if (n + 1) then γ₀‖l‖ else γ₀‖r‖⟩ ⭢ ⟦j⟧ ⟨σ₂, v₀⟩
    -- ——————————————————————————————————————————————————————
    -- i + 1 = j
    -- ⟨σ₀, γ₀‖r‖⟩ ⭢* ⟦i⟧ ⟨σ₂, v₀⟩
    simp at Hstep₀
    have ⟨i, HEqj, Hstep₀⟩ := stepn_indexed.refine.ifz₁_else.eliminator _ _ _ _ _ _ _ Hvalue₀ Hstep₀
    --
    --
    -- ⟨σ₀, γ₀‖r‖⟩ ⭢* ⟦i⟧ ⟨σ₂, v₀⟩
    -- ‖Γ‖ ⊧ ‖r‖ ≤𝑙𝑜𝑔 ‖r‖ : ‖τ‖
    -- ——————————————————————————————
    -- ⟨σ₁, γ₁‖r‖⟩ ⭢* ⟨σ₃, v₁⟩
    -- (σ₂, σ₃) : 𝓦₁
    -- (k - i, 𝓦₁, v₀, v₁) ∈ 𝓥⟦‖τ‖⟧
    have ⟨_, _, IH⟩ := log_approx.fundamental _ _ _ HEτ₁
    simp only [log_approx_expr] at IH
    have ⟨𝓦₁, σ₃, v₁, Hfuture₀, Hstep₁, Hsem_store, Hsem_value⟩ := IH _ _ _ _ HsemΓ i (by omega) _ _ Hsem_store _ _ Hvalue₀ Hstep₀
    have ⟨_, Hfuture₀⟩ := Hfuture₀
    exists 𝓦₁, σ₃, v₁
    constructor
    . constructor; omega; apply Hfuture₀
    constructor
    . apply Hstep₁
    constructor
    . apply Hsem_store
    . apply log_approx_value.antimono
      apply Hsem_value; simp; omega
  -- right approximation
  . have HEτ₀ := typing.erase.safety _ _ _ _ _ Hτ₁
    have HEτ₁ := typing.erase.safety _ _ _ _ _ Hτ₀
    constructor; apply HEτ₀
    constructor; apply HEτ₁
    intros k 𝓦₀ γ₀ γ₁ HsemΓ
    have ⟨Hmwf₀, Hmwf₁⟩ := log_approx_env.syntactic.mwf _ _ _ _ _ HsemΓ
    simp only [log_approx_expr]
    intros j Hindexj σ₀ σ₁ Hsem_store σ₂ v₀ Hvalue₀ Hstep₀
    --
    --
    -- ⟨σ₀, γ₀‖r‖⟩ ⭢* ⟦j⟧ ⟨σ₂, v₀⟩
    -- ‖Γ‖ ⊧ ‖r‖ ≤𝑙𝑜𝑔 ‖r‖ : ‖τ‖
    -- ——————————————————————————————
    -- ⟨σ₁, γ₁‖r‖⟩ ⭢* ⟨σ₃, v₁⟩
    -- (σ₂, σ₃) : 𝓦₁
    -- (k - j, 𝓦₁, v₀, v₁) ∈ 𝓥⟦‖τ‖⟧
    have ⟨_, _, IH⟩ := log_approx.fundamental _ _ _ HEτ₀
    simp only [log_approx_expr] at IH
    have ⟨𝓦₁, σ₃, v₁, Hfuture₀, Hstep₁, Hsem_store, Hsem_value⟩ := IH _ _ _ _ HsemΓ j (by omega) _ _ Hsem_store _ _ Hvalue₀ Hstep₀
    have ⟨_, Hfuture₀⟩ := Hfuture₀
    exists 𝓦₁, σ₃, v₁
    constructor
    . constructor; omega; apply Hfuture₀
    constructor
    . apply stepn.multi _ _ _ _ Hstep₁
      apply step_lvl.pure _ _ _ _ ctx𝕄.hole
      . apply lc.under_msubst _ _ _ Hmwf₁
        apply typing.regular _ _ _ _ _ HEτ₁
      . simp; apply head_pure.ifz₁_else
    constructor
    . apply Hsem_store
    . apply Hsem_value

theorem semantics_preservation.pure.head :
  ∀ Γ e₀ e₁ τ φ,
    e₀ ↝ e₁ →
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
