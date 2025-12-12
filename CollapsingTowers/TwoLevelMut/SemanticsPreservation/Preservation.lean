import CollapsingTowers.TwoLevelMut.SemanticsPreservation.PresvCtx
import CollapsingTowers.TwoLevelMut.SemanticsPreservation.PresvPure
import CollapsingTowers.TwoLevelMut.SemanticsPreservation.PresvReflect

-- ⟨σ₀, e₀⟩ ⇝ ⟨σ₁, e₁⟩ (under Γ)
-- Γ ⊢ e₀ : τ
-- ——————————————————————————————
-- ‖Γ‖ ⊨ ‖e₀‖ ≈𝑙𝑜𝑔 ‖e₁‖ : ‖τ‖
theorem semantics_preservation.strengthened :
  ∀ Γ σ₀ σ₁ e₀ e₁ τ φ,
    step_lvl Γ.length ⟨σ₀, e₀⟩ ⟨σ₁, e₁⟩ →
    typing Γ 𝟙 e₀ τ φ →
    log_equiv (erase_env Γ) ‖e₀‖ ‖e₁‖ (erase_ty τ) :=
  by
  intros Γ σ₀ σ₁ e₀ e₁ τ φ
  generalize HEqlvl : Γ.length = lvl
  intros Hstep Hτ
  cases Hstep
  case pure HM Hlc Hhead =>
    induction HM generalizing Γ τ φ
    case hole =>
      apply semantics_preservation.pure.head
      apply Hhead; apply Hτ
    case cons𝔹 B M HB HM IH =>
      rw [← ctx_comp B M, ← ctx_comp B M]
      apply semantics_preservation.under_ctx𝔹; apply HB
      intros _ _; apply IH
      apply HEqlvl; apply Hτ
    case consℝ R M HR HM IH =>
      rw [← ctx_comp R M, ← ctx_comp R M]
      apply semantics_preservation.under_ctxℝ; rw [HEqlvl]; apply HR
      apply lc.under_ctx𝕄; apply HM; apply Hlc
      intros _ _ _ _; apply IH
      omega; apply Hτ
  case mutable HM Hlc Hmut =>
    exfalso; rw [← HEqlvl] at HM
    apply preservation.mutable _ _ _ _ _ _ _ _ HM Hlc Hmut Hτ
  case reflect HP HE Hlc =>
    cases HP
    case hole =>
      apply semantics_preservation.reflect.head; apply HE; apply Hτ
    case consℚ HQ =>
      induction HQ generalizing Γ τ φ
      case holeℝ HR =>
        apply semantics_preservation.under_ctxℝ; rw [HEqlvl]; apply HR
        apply lc.under_ctx𝔼; apply HE; apply Hlc
        intros _ _ _ _ Hτ
        apply semantics_preservation.reflect.head; apply HE; apply Hτ
        apply Hτ
      case cons𝔹 B Q HB HQ IH =>
        rw [← ctx_comp B Q]
        apply semantics_preservation.under_ctx𝔹; apply HB
        intros _ _; apply IH
        apply HEqlvl; apply Hτ
      case consℝ R Q HR HQ IH =>
        rw [← ctx_comp R Q]
        apply semantics_preservation.under_ctxℝ; rw [HEqlvl]; apply HR
        apply lc.under_ctxℚ; apply HQ
        apply lc.under_ctx𝔼; apply HE; apply Hlc
        intros _ _ _ _; apply IH
        omega; apply Hτ

theorem semantics_preservation :
  ∀ σ₀ σ₁ e₀ e₁ τ φ,
    (⟨σ₀, e₀⟩ ⇝ ⟨σ₁, e₁⟩) →
    typing_reification ⦰ e₀ τ φ →
    ctx_equiv ⦰ ‖e₀‖ ‖e₁‖ (erase_ty τ) :=
  by
  intros σ₀ σ₁ e₀ e₁ τ φ Hstep Hτ
  cases Hτ
  all_goals next Hτ =>
    apply log_equiv.soundness
    apply semantics_preservation.strengthened ⦰ _ _ _ _ _ _ Hstep Hτ

-- ⟨σ₀, e₀⟩ ⇝* ⟨σ₁, e₁⟩
-- ∅ ⊢ e₀ : τ
-- ————————————————————————
-- ∅ ⊨ ‖e₀‖ ≈𝑐𝑡𝑥 ‖e₁‖ : ‖τ‖
theorem semantics_preservation.stepn :
  ∀ σ₀ σ₁ e₀ e₁ τ φ,
    (⟨σ₀, e₀⟩ ⇝* ⟨σ₁, e₁⟩) →
    typing_reification ⦰ e₀ τ φ →
    ctx_equiv ⦰ ‖e₀‖ ‖e₁‖ (erase_ty τ) :=
  by
  intro σ₀ σ₂ e₀ e₂ τ φ₀ Hstepn Hτ₀
  generalize HEq₀ : (σ₀, e₀) = st₀
  generalize HEq₁ : (σ₂, e₂) = st₂
  rw [HEq₀, HEq₁] at Hstepn
  induction Hstepn generalizing φ₀ σ₀ e₀
  case refl =>
    simp [← HEq₀] at HEq₁
    rw [HEq₁.right]
    cases Hτ₀
    all_goals next Hτ₀ =>
      apply log_equiv.soundness
      apply log_equiv.fundamental
      apply typing.erase.safety _ _ _ _ _ Hτ₀
  case multi st₀ st₁ st₂ Hstep Hstepn IH =>
    rcases st₁ with ⟨σ₁, e₁⟩
    rw [← HEq₀] at Hstep
    have ⟨_, Hτ₁, _⟩ := preservation _ _ _ _ _ _ Hstep Hτ₀
    apply ctx_equiv.trans
    . apply semantics_preservation _ _ _ _ _ _ Hstep Hτ₀
    . apply IH; apply Hτ₁; rfl; apply HEq₁

-- ⟨σ₀, e₀⟩ ⇝* ⟨σ₁, v⟩
-- ∅ ⊢ e₀ : <τ>
-- ————————————————————
-- v = code e₁
-- ∅ ⊢ ‖e₀‖ ≈𝑐𝑡𝑥 e₁ : τ
theorem semantics_preservation.stepn.rep :
  ∀ σ₀ σ₁ e₀ v τ φ,
    (⟨σ₀, e₀⟩ ⇝* ⟨σ₁, v⟩) → value v →
    typing_reification ⦰ e₀ (.rep τ) φ →
    ∃ e₁,
      v = .code e₁ ∧
      ctx_equiv ⦰ ‖e₀‖ e₁ τ :=
  by
  intros σ₀ σ₁ e₀ v τ φ Hstepn Hvalue Hτr₀
  have ⟨_, Hτr₁, _⟩ := preservation.stepn _ _ _ _ _ _ Hstepn Hτr₀
  cases Hvalue <;> try contradiction
  case code e₁ _ =>
  have Hτe₁ := typing_reification_code _ _ _ _ Hτr₁
  have HGe₁ := typing.dynamic_impl_grounded _ _ _ _ Hτe₁
  have ⟨Hwbt, _⟩ := typing.dynamic_impl_pure _ _ _ _ Hτe₁
  exists e₁
  constructor; rfl
  rw [← (grounded_iff_erase_identity e₁).mp HGe₁, ← (grounded_ty_iff_erase_identity _).mp Hwbt]
  apply semantics_preservation.stepn _ _ _ _ _ _ Hstepn Hτr₀
