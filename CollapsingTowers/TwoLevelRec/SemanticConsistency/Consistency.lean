import CollapsingTowers.TwoLevelRec.SemanticConsistency.ConsisCtx
import CollapsingTowers.TwoLevelRec.SemanticConsistency.ConsisPure
import CollapsingTowers.TwoLevelRec.SemanticConsistency.ConsisReflect

-- e₀ ⇝ e₁ (under Γ)
-- Γ ⊢ e₀ : τ
-- ——————————————————————————
-- ‖Γ‖ ⊨ ‖e₀‖ ≈𝑙𝑜𝑔 ‖e₁‖ : ‖τ‖
theorem consistency.strengthened :
  ∀ Γ e₀ e₁ τ φ,
    step_lvl Γ.length e₀ e₁ →
    typing Γ 𝟙 e₀ τ φ →
    log_equiv (erase_env Γ) ‖e₀‖ ‖e₁‖ (erase_ty τ) :=
  by
  intros Γ e₀ e₁ τ φ
  generalize HEqlvl : Γ.length = lvl
  intros Hstep Hτ
  cases Hstep
  case pure HM Hlc Hhead =>
    induction HM generalizing Γ τ φ
    case hole =>
      apply consistency.pure.head
      apply Hhead; apply Hτ
    case cons𝔹 B M HB HM IH =>
      rw [← ctx_comp B M, ← ctx_comp B M]
      apply consistency.under_ctx𝔹; apply HB
      intros _ _; apply IH
      apply HEqlvl; apply Hτ
    case consℝ R M HR HM IH =>
      rw [← ctx_comp R M, ← ctx_comp R M]
      apply consistency.under_ctxℝ; rw [HEqlvl]; apply HR
      apply lc.under_ctx𝕄; apply HM; apply Hlc
      intros _ _ _ _; apply IH
      omega; apply Hτ
  case reflect HP HE Hlc =>
    cases HP
    case hole =>
      apply consistency.reflect.head; apply HE; apply Hτ
    case consℚ HQ =>
      induction HQ generalizing Γ τ φ
      case holeℝ HR =>
        apply consistency.under_ctxℝ; rw [HEqlvl]; apply HR
        apply lc.under_ctx𝔼; apply HE; apply Hlc
        intros _ _ _ _ Hτ
        apply consistency.reflect.head; apply HE; apply Hτ
        apply Hτ
      case cons𝔹 B Q HB HQ IH =>
        rw [← ctx_comp B Q]
        apply consistency.under_ctx𝔹; apply HB
        intros _ _; apply IH
        apply HEqlvl; apply Hτ
      case consℝ R Q HR HQ IH =>
        rw [← ctx_comp R Q]
        apply consistency.under_ctxℝ; rw [HEqlvl]; apply HR
        apply lc.under_ctxℚ; apply HQ
        apply lc.under_ctx𝔼; apply HE; apply Hlc
        intros _ _ _ _; apply IH
        omega; apply Hτ

theorem consistency :
  ∀ e₀ e₁ τ φ,
    (e₀ ⇝ e₁) →
    typing_reification ⦰ e₀ τ φ →
    log_equiv ⦰ ‖e₀‖ ‖e₁‖ (erase_ty τ) :=
  by
  intros e₀ e₁ τ φ Hstep Hτ
  cases Hτ
  all_goals next Hτ =>
    apply consistency.strengthened ⦰ _ _ _ _ Hstep Hτ

-- e₀ ⇝* e₁
-- ∅ ⊢ e₀ : τ
-- ————————————————————————
-- ∅ ⊨ ‖e₀‖ ≈𝑙𝑜𝑔 ‖e₁‖ : ‖τ‖
theorem consistency.stepn :
  ∀ e₀ e₁ τ φ,
    (e₀ ⇝* e₁) →
    typing_reification ⦰ e₀ τ φ →
    log_equiv ⦰ ‖e₀‖ ‖e₁‖ (erase_ty τ) :=
  by
  intros e₀ e₁ τ φ Hstepn Hτ₀
  induction Hstepn generalizing φ
  case refl =>
    cases Hτ₀
    all_goals next Hτ₀ =>
      constructor
      . apply log_approx.fundamental
        apply typing.erase.safety _ _ _ _ _ Hτ₀
      . apply log_approx.fundamental
        apply typing.erase.safety _ _ _ _ _ Hτ₀
  case multi Hstep Hstepn IH =>
    have ⟨_, Hτ₁, _⟩ := preservation _ _ _ _ Hstep Hτ₀
    apply log_equiv.trans
    . apply consistency _ _ _ _ Hstep Hτ₀
    . apply IH; apply Hτ₁

-- e₀ ⇝* v
-- ∅ ⊢ e₀ : <τ>
-- ————————————————————
-- v = code e₁
-- ∅ ⊢ ‖e₀‖ ≈𝑙𝑜𝑔 e₁ : τ
theorem consistency.stepn.rep :
  ∀ e₀ v τ φ,
    (e₀ ⇝* v) → value v →
    typing_reification ⦰ e₀ (.rep τ) φ →
    ∃ e₁,
      v = .code e₁ ∧
      log_equiv ⦰ ‖e₀‖ e₁ τ :=
  by
  intros e₀ v τ φ Hstepn Hvalue Hτr₀
  have ⟨_, Hτr₁, _⟩ := preservation.stepn _ _ _ _ Hstepn Hτr₀
  cases Hvalue <;> try contradiction
  case code e₁ _ =>
  have Hτe₁ := typing_reification_code _ _ _ _ Hτr₁
  have HGe₁ := typing.dynamic_impl_grounded _ _ _ _ Hτe₁
  have ⟨Hwbt, _⟩ := typing.dynamic_impl_pure _ _ _ _ Hτe₁
  exists e₁
  constructor; rfl
  rw [← (grounded_iff_erase_identity e₁).mp HGe₁, ← (grounded_ty_iff_erase_identity _).mp Hwbt]
  apply consistency.stepn _ _ _ _ Hstepn Hτr₀
