
import CollapsingTowers.TwoLevelBasic.SemEquiv.Fundamental
theorem multi_subst_erase_value :
  ∀ Γ v τ φ γ₀ γ₁,
    typing Γ .stat v τ φ →
    sem_equiv_env γ₀ γ₁ (erase_env Γ) →
    value v →
    well_binding_time .stat τ →
    value (multi_subst γ₀ (erase v)) :=
  by
  intros Γ v τ φ γ₀ γ₁ Hτ HsemΓ Hvalue HwellBinds
  have ⟨Hmulti_wf₀, Hmulti_wf₁⟩ := sem_equiv_env_impl_multi_wf _ _ _ HsemΓ
  cases Hvalue
  case lam Hlc =>
    simp; apply value.lam
    apply multi_subst_lc_at; apply Hmulti_wf₀
    apply erase_lc_at; apply Hlc
  case lit =>
    simp; apply value.lit
  case code e _ =>
    cases e <;> cases Hτ <;> try simp at HwellBinds
    apply And.left; apply sem_equiv_value_impl_value
    apply sem_equiv_env_impl_sem_equiv_value
    apply HsemΓ; apply binds_erase_env; assumption

theorem sem_preservation_head :
  ∀ Γ e₀ e₁ τ φ,
    head𝕄 e₀ e₁ →
    typing Γ .stat e₀ τ φ →
    typing Γ .stat e₁ τ φ →
    sem_equiv_typing (erase_env Γ) (erase e₀) (erase e₁) (erase_ty τ) :=
  by
  intros Γ e₀ e₁ τ φ Hhead Hτ₀ Hτ₁
  cases Hhead <;> try apply fundamental; apply Hτ₀
  case lets Hvalue =>
    intros γ₀ γ₁ HsemΓ
    have ⟨Hmulti_wf₀, Hmulti_wf₁⟩ := sem_equiv_env_impl_multi_wf _ _ _ HsemΓ
    apply sem_equiv_expr_stepn
    apply fundamental; apply Hτ₁; apply HsemΓ
    . apply pure_stepn.multi; apply pure_stepn.refl
      rw [erase_open_subst_comm, multi_subst_open_subst_comm _ _ _ Hmulti_wf₀]
      apply pure_step.pure_step𝕄 id; apply ctx𝕄.hole
      apply multi_subst_lc_at; apply Hmulti_wf₀; apply erase_lc_at; apply typing_regular; apply Hτ₀
      simp; apply head𝕄.lets
      cases Hτ₀ with
      | lets _ _ _ _ _ _ _ _ Hτv _ HwellBinds _ =>
          apply multi_subst_erase_value
          apply Hτv; apply HsemΓ; apply Hvalue; apply HwellBinds
    . apply pure_stepn.refl
  case app₁ Hvalue =>
    --
    --
    -- value v
    -- ——————————————————————————————————
    -- |Γ| ⊧ |λ.e @ v| ≈ |e⟦0 ↦ v⟧| : |τ|
    --
    --
    -- value v
    -- (γ₀, γ₁) ∈ 𝓖⟦Γ⟧
    -- ————————————————————————————————————————
    -- (γ₀(|λ.e @ v|), γ₁(|e⟦0 ↦ v⟧|)) ∈ 𝓔⟦|τ|⟧
    --
    --
    -- value v
    -- (γ₀, γ₁) ∈ 𝓖⟦Γ⟧
    -- ————————————————————————————————————————————————————
    -- (λ.γ₀(|e|) @ γ₀(|v|), γ₁(|e|)⟦0 ↦ γ₁(|v|)⟧) ∈ 𝓔⟦|τ|⟧
    --
    --
    -- value v
    -- ————————————————————————————————————————————
    -- λ.γ₀(|e|) @ γ₀(|v|) ↦* γ₁(|e|)⟦0 ↦ γ₁(|v|)⟧
    --
    --
    -- value v
    -- —————————————
    -- value γ₀(|v|)
    --
    --
    -- value n  value λ.e        value (code x)  value (code e)
    -- ———————  ———————————————  ——————————————  ——————————————————
    -- value n  value λ.γ₀(|e|)  value γ₀(x)     Binding Time Error
    intros γ₀ γ₁ HsemΓ
    have ⟨Hmulti_wf₀, Hmulti_wf₁⟩ := sem_equiv_env_impl_multi_wf _ _ _ HsemΓ
    apply sem_equiv_expr_stepn
    apply fundamental; apply Hτ₁; apply HsemΓ
    . apply pure_stepn.multi; apply pure_stepn.refl
      rw [erase_open_subst_comm, multi_subst_open_subst_comm _ _ _ Hmulti_wf₀]
      apply pure_step.pure_step𝕄 id; apply ctx𝕄.hole
      apply multi_subst_lc_at; apply Hmulti_wf₀; apply erase_lc_at; apply typing_regular; apply Hτ₀
      simp; apply head𝕄.app₁
      cases Hτ₀ with
      | app₁ _ _ _ _ _ _ _ _ _ Hτe Hτv =>
        cases Hτe with
        | lam _ _ _ _ _ _ _ HwellBinds =>
          apply multi_subst_erase_value
          apply Hτv; apply HsemΓ; apply Hvalue; apply HwellBinds
    . apply pure_stepn.refl
  case lift_lam e =>
    have HEq : erase (.lam𝕔 (map𝕔₀ e)) = erase (.lift (.lam e)) :=
      by simp [erase_maping𝕔]
    rw [HEq]; apply fundamental; apply Hτ₀

theorem sem_preservation_strengthened :
  ∀ Γ e₀ e₁ τ φ,
    step_lvl Γ.length e₀ e₁ →
    typing Γ .stat e₀ τ φ →
    sem_equiv_typing (erase_env Γ) (erase e₀) (erase e₁) (erase_ty τ) :=
  by
  intros Γ e₀ e₁ τ φ
  generalize HEqlvl : Γ.length = lvl
  intros Hstep Hτ
  cases Hstep
  case step𝕄 HM Hlc Hhead𝕄 =>
    induction HM generalizing Γ τ φ
    case hole =>
      apply sem_preservation_head
      apply Hhead𝕄; apply Hτ
      admit
    case cons𝔹 HB HM IH =>
      admit
    case consℝ =>
      admit
  case reflect => admit
