import CollapsingTowers.TwoLevelRec.OperationalSemantics.SmallStep

lemma pure_step.congruence_under_ctx𝔹 : ∀ B e₀ e₁, ctx𝔹 B → (e₀ ⇾ e₁) → (B⟦e₀⟧ ⇾ B⟦e₁⟧) :=
  by
  intros B e₀ e₁ HB Hstep
  cases Hstep
  case pure M _ _ HM Hlc Hhead =>
    rw [ctx_comp B M]
    apply pure_step.pure
    apply ctx𝕄.cons𝔹; apply HB; apply HM
    apply Hlc; apply Hhead

lemma pure_step.congruence_under_ctx𝔼 : ∀ E e₀ e₁, ctx𝔼 E → (e₀ ⇾ e₁) → (E⟦e₀⟧ ⇾ E⟦e₁⟧) :=
  by
  intros E e₀ e₁ HE Hstep
  induction HE
  case hole => apply Hstep
  case cons𝔹 HB _ IH =>
    simp; apply congruence_under_ctx𝔹
    apply HB; apply IH

lemma pure_stepn.congruence_under_ctx𝔹 : ∀ B e₀ e₁, ctx𝔹 B → (e₀ ⇾* e₁) → (B⟦e₀⟧ ⇾* B⟦e₁⟧) :=
  by
  intros B e₀ e₁ HB Hstepn
  induction Hstepn
  case refl => apply pure_stepn.refl
  case multi H _ IH =>
    apply pure_stepn.multi
    apply pure_step.congruence_under_ctx𝔹
    apply HB; apply H; apply IH

lemma pure_stepn.congruence_under_ctx𝔼 : ∀ E e₀ e₁, ctx𝔼 E → (e₀ ⇾* e₁) → (E⟦e₀⟧ ⇾* E⟦e₁⟧) :=
  by
  intros E e₀ e₁ HE Hstepn
  induction Hstepn
  case refl => apply pure_stepn.refl
  case multi H _ IH =>
    apply pure_stepn.multi
    apply pure_step.congruence_under_ctx𝔼
    apply HE; apply H; apply IH

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
