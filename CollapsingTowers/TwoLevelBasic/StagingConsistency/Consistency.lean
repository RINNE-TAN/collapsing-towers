import CollapsingTowers.TwoLevelBasic.StagingConsistency.ConsisHead
import CollapsingTowers.TwoLevelBasic.StagingConsistency.ConsisReflect

-- e₀ ⇝ e₁ (under Γ)
-- Γ ⊢ e₀ : τ
-- ———————————————————————
-- ‖Γ‖ ⊨ ‖e₀‖ ≈ ‖e₁‖ : ‖τ‖
theorem consistency.strengthened :
  ∀ Γ e₀ e₁ τ φ,
    step_lvl Γ.length e₀ e₁ →
    typing Γ 𝟙 e₀ τ φ →
    log_equiv_typing ‖Γ‖𝛾 ‖e₀‖ ‖e₁‖ ‖τ‖𝜏 :=
  by
  intros Γ e₀ e₁ τ φ
  generalize HEqlvl : Γ.length = lvl
  intros Hstep Hτ
  cases Hstep
  case pure HM Hlc Hhead =>
    induction HM generalizing Γ τ φ
    case hole =>
      apply consistency.head
      apply Hhead; apply Hτ
      apply preservation.head
      apply Hhead; apply Hlc; apply Hτ
    case cons𝔹 B M HB HM IH =>
      rw [← ctx_comp B M]
      apply consistency.under_ctx𝔹; apply HB
      intros _ _; apply IH
      apply HEqlvl; apply Hτ
    case consℝ R M HR HM IH =>
      rw [← ctx_comp R M]
      apply consistency.under_ctxℝ; rw [HEqlvl]; apply HR
      apply lc.under_ctx𝕄; apply HM; apply Hlc
      intros _ _ _ HEqintro; apply IH
      simp; omega; apply Hτ
  case reflect HP HE Hlc =>
    cases HP
    case hole => apply consistency.reflect; apply HE; apply Hτ
    case consℚ HQ =>
      induction HQ generalizing Γ τ φ
      case holeℝ HR =>
        apply consistency.under_ctxℝ; rw [HEqlvl]; apply HR
        apply lc.under_ctx𝔼; apply HE; apply Hlc
        intros _ _ _ _ Hτ
        apply consistency.reflect; apply HE; apply Hτ; apply Hτ
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
        intros _ _ _ HEqintro; apply IH
        simp; omega; apply Hτ

theorem consistency :
  ∀ e₀ e₁ τ φ,
    (e₀ ⇝ e₁) →
    typing_reification [] e₀ τ φ →
    log_equiv_typing [] ‖e₀‖ ‖e₁‖ ‖τ‖𝜏 :=
  by
  intros e₀ e₁ τ φ Hstep Hτ
  cases Hτ
  case pure Hτ =>
    apply consistency.strengthened []
    apply Hstep; apply Hτ
  case reify τ Hτ =>
    apply consistency.strengthened [] _ _ (.fragment τ)
    apply Hstep; apply Hτ

-- e₀ ⇝* e₁
-- ∅ ⊢ e₀ : τ
-- —————————————————————
-- ∅ ⊨ ‖e₀‖ ≈ ‖e₁‖ : ‖τ‖
theorem consistency.stepn :
  ∀ e₀ e₁ τ φ,
    (e₀ ⇝* e₁) →
    typing_reification [] e₀ τ φ →
    log_equiv_typing [] ‖e₀‖ ‖e₁‖ ‖τ‖𝜏 :=
  by
  intros e₀ e₁ τ φ Hstepn Hτ₀
  induction Hstepn generalizing φ
  case refl => apply typing_reification.erase.fundamental _ _ _ _ Hτ₀
  case multi Hstep Hstepn IH =>
    have ⟨_, Hτ₁, _⟩ := preservation _ _ _ _ Hstep Hτ₀
    apply log_equiv_typing.trans
    . apply consistency _ _ _ _ Hstep Hτ₀
    . apply IH; apply Hτ₁

-- e₀ ⇝* v
-- ∅ ⊢ e₀ : <τ>
-- ————————————————————
-- v = code e₁
-- ∅ ⊢ ‖e₀‖ ≈ e₁ : τ
theorem consistency.stepn.rep :
  ∀ e₀ v τ φ,
    (e₀ ⇝* v) →
    value v →
    typing_reification [] e₀ (.rep τ) φ →
    ∃ e₁,
      v = .code e₁ ∧
      log_equiv_typing [] ‖e₀‖ e₁ τ :=
  by
  intros e₀ v τ φ Hstepn Hvalue Hτr₀
  have ⟨_, Hτr₁, _⟩ := preservation.stepn _ _ _ _ Hstepn Hτr₀
  have ⟨e₁, HEq, Hτe₁⟩ := typing.rep_ty_iff_value_code _ _ _ Hvalue Hτr₁
  rw [HEq] at Hstepn
  exists e₁
  constructor; apply HEq
  rw [← identity.erase_typing_dyn _ _ _ _ Hτe₁, ← identity.ty.erase_typing_dyn _ _ _ _ Hτe₁]
  apply consistency.stepn _ _ _ _ Hstepn Hτr₀
