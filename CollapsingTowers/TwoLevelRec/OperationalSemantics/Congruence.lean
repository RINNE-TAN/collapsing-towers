import CollapsingTowers.TwoLevelRec.OperationalSemantics.SmallStep

lemma step.congruence_under_ctx𝔹.grounded : ∀ B e₀ e₁, ctx𝔹 B → grounded e₀ → (e₀ ⇝ e₁) → (B⟦e₀⟧ ⇝ B⟦e₁⟧) :=
  by
  intros B e₀ e₁ HB HG Hstep
  cases Hstep
  case pure M _ _ HM Hlc Hhead =>
    rw [ctx_comp B M]
    apply step_lvl.pure
    apply ctx𝕄.cons𝔹; apply HB; apply HM
    apply Hlc; apply Hhead
  case reflect M E _ HP HE _ =>
    have HM := rewrite.ctxℙ_ctx𝕄 _ _ HP
    have HG := grounded.under_ctx𝕄 _ _ _ HM HG
    have HG := grounded.under_ctx𝔼 _ _ HE HG
    simp at HG

lemma stepn.congruence_under_ctx𝔹.grounded : ∀ B e₀ e₁, ctx𝔹 B → grounded e₀ → (e₀ ⇝* e₁) → (B⟦e₀⟧ ⇝* B⟦e₁⟧) :=
  by
  intros B e₀ e₁ HB HG Hstepn
  induction Hstepn
  case refl => apply stepn.refl
  case multi H _ IH =>
    apply stepn.multi
    apply step.congruence_under_ctx𝔹.grounded
    apply HB; apply HG; apply H
    apply IH; admit

lemma step.congruence_under_ctx𝔹 : ∀ lvl B e₀ e₁, ctx𝔹 B → step_lvl lvl e₀ e₁ → ∃ e₂, step_lvl lvl B⟦e₀⟧ e₂ :=
  by
  intros lvl B e₀ e₁ HB Hstep
  cases Hstep with
  | pure M _ _ HM Hlc Hhead =>
    rw [ctx_comp B M]
    constructor; apply step_lvl.pure
    apply ctx𝕄.cons𝔹; apply HB; apply HM
    apply Hlc; apply Hhead
  | reflect P E _ HP HE Hlc =>
    cases HP
    case hole =>
      constructor
      rw [ctx_swap B, ctx_comp B E]
      apply step_lvl.reflect
      apply ctxℙ.hole; apply ctx𝔼.cons𝔹
      apply HB; apply HE; apply Hlc
    case consℚ HQ =>
      constructor
      rw [ctx_comp B P]
      apply step_lvl.reflect
      apply ctxℙ.consℚ; apply ctxℚ.cons𝔹
      apply HB; apply HQ; apply HE; apply Hlc

lemma step.congruence_under_ctxℝ : ∀ intro lvl R e₀ e₁, ctxℝ intro lvl R → step_lvl (lvl + intro) e₀ e₁ → step_lvl lvl R⟦e₀⟧ R⟦e₁⟧ :=
  by
  intros intro lvl R e₀ e₁ HR Hstep
  cases Hstep with
  | pure M _ _ HM Hlc Hhead =>
    repeat rw [ctx_comp R M]
    apply step_lvl.pure
    apply ctx𝕄.consℝ; apply HR; apply HM
    apply Hlc; apply Hhead
  | reflect P _ _ HP HE Hlc =>
    cases HP
    case hole =>
      apply step_lvl.reflect
      apply ctxℙ.consℚ; apply ctxℚ.holeℝ
      apply HR; apply HE; apply Hlc
    case consℚ HQ =>
      rw [ctx_comp R P]
      apply step_lvl.reflect
      apply ctxℙ.consℚ; apply ctxℚ.consℝ
      apply HR; apply HQ; apply HE; apply Hlc
