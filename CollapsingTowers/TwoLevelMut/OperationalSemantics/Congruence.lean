import CollapsingTowers.TwoLevelMut.OperationalSemantics.SmallStep

lemma step_grounded.congruence_under_ctx𝔹 : ∀ B σ₀ σ₁ e₀ e₁, ctx𝔹 B → grounded e₀ → (⟨σ₀, e₀⟩ ⇝ ⟨σ₁, e₁⟩) → (⟨σ₀, B⟦e₀⟧⟩ ⇝ ⟨σ₁, B⟦e₁⟧⟩) :=
  by
  intros B σ₀ σ₁ e₀ e₁ HB HG Hstep
  cases Hstep
  case pure M _ _ HM Hlc Hhead =>
    repeat rw [ctx_comp B M]
    apply step_lvl.pure
    apply ctx𝕄.cons𝔹; apply HB; apply HM
    apply Hlc; apply Hhead
  case mutable M _ _ HM Hlc Hmut =>
    repeat rw [ctx_comp B M]
    apply step_lvl.mutable
    apply ctx𝕄.cons𝔹; apply HB; apply HM
    apply Hlc; apply Hmut
  case reflect M E _ HP HE _ =>
    have HM := rewrite.ctxℙ_ctx𝕄 _ _ HP
    have HG := grounded.decompose_ctx𝕄 _ _ _ HM HG
    have HG := grounded.decompose_ctx𝔼 _ _ HE HG
    simp at HG

lemma step_grounded.congruence_under_ctx𝔼 : ∀ E σ₀ σ₁ e₀ e₁, ctx𝔼 E → grounded e₀ → (⟨σ₀, e₀⟩ ⇝ ⟨σ₁, e₁⟩) → (⟨σ₀, E⟦e₀⟧⟩ ⇝ ⟨σ₁, E⟦e₁⟧⟩) :=
  by
  intros E σ₀ σ₁ e₀ e₁ HE HG Hstep
  cases Hstep
  case pure M _ _ HM Hlc Hhead =>
    rw [ctx_comp E M]
    apply step_lvl.pure
    apply compose.ctx𝔼_ctx𝕄; apply HM; apply HE
    apply Hlc; apply Hhead
  case mutable M _ _ HM Hlc Hmut =>
    rw [ctx_comp E M]
    apply step_lvl.mutable
    apply compose.ctx𝔼_ctx𝕄; apply HM; apply HE
    apply Hlc; apply Hmut
  case reflect M E _ HP HE _ =>
    have HM := rewrite.ctxℙ_ctx𝕄 _ _ HP
    have HG := grounded.decompose_ctx𝕄 _ _ _ HM HG
    have HG := grounded.decompose_ctx𝔼 _ _ HE HG
    simp at HG

lemma stepn_grounded.congruence_under_ctx𝔹 : ∀ B σ₀ σ₁ e₀ e₁, ctx𝔹 B → grounded e₀ → (⟨σ₀, e₀⟩ ⇝* ⟨σ₁, e₁⟩) → (⟨σ₀, B⟦e₀⟧⟩ ⇝* ⟨σ₁, B⟦e₁⟧⟩) :=
  by
  intros B σ₀ σ₂ e₀ e₂ HB HG Hstepn
  generalize HEq₀ : (σ₀, e₀) = st₀
  generalize HEq₁ : (σ₂, e₂) = st₂
  rw [HEq₀, HEq₁] at Hstepn
  induction Hstepn generalizing σ₀ e₀
  case refl st₁ =>
    rcases st₁ with ⟨σ₁, e₁⟩
    simp at HEq₀ HEq₁
    simp [HEq₀, HEq₁]
    apply stepn.refl
  case multi st₀ st₁ st₂ Hstep Hstepn IH =>
    rcases st₁ with ⟨σ₁, e₁⟩
    rw [← HEq₀] at Hstep
    apply stepn.multi
    apply step_grounded.congruence_under_ctx𝔹
    apply HB; apply HG; apply Hstep
    apply IH _ _ (grounded.under_step _ _ _ _ Hstep HG) rfl HEq₁

lemma stepn_grounded.congruence_under_ctx𝔼 : ∀ E σ₀ σ₁ e₀ e₁, ctx𝔼 E → grounded e₀ → (⟨σ₀, e₀⟩ ⇝* ⟨σ₁, e₁⟩) → (⟨σ₀, E⟦e₀⟧⟩ ⇝* ⟨σ₁, E⟦e₁⟧⟩) :=
  by
  intros E σ₀ σ₂ e₀ e₂ HE HG Hstepn
  generalize HEq₀ : (σ₀, e₀) = st₀
  generalize HEq₁ : (σ₂, e₂) = st₂
  rw [HEq₀, HEq₁] at Hstepn
  induction Hstepn generalizing σ₀ e₀
  case refl st₁ =>
    rcases st₁ with ⟨σ₁, e₁⟩
    simp at HEq₀ HEq₁
    simp [HEq₀, HEq₁]
    apply stepn.refl
  case multi st₀ st₁ st₂ Hstep Hstepn IH =>
    rcases st₁ with ⟨σ₁, e₁⟩
    rw [← HEq₀] at Hstep
    apply stepn.multi
    apply step_grounded.congruence_under_ctx𝔼
    apply HE; apply HG; apply Hstep
    apply IH _ _ (grounded.under_step _ _ _ _ Hstep HG) rfl HEq₁

lemma step.congruence_under_ctx𝔹 :
  ∀ lvl B σ₀ σ₁ e₀ e₁,
    ctx𝔹 B →
    step_lvl lvl ⟨σ₀, e₀⟩ ⟨σ₁, e₁⟩ →
    ∃ e₂,
    step_lvl lvl ⟨σ₀, B⟦e₀⟧⟩ ⟨σ₁, e₂⟩ :=
  by
  intros lvl B σ₀ σ₁ e₀ e₁ HB Hstep
  cases Hstep with
  | pure M _ _ _ HM Hlc Hhead =>
    rw [ctx_comp B M]
    constructor; apply step_lvl.pure
    apply ctx𝕄.cons𝔹; apply HB; apply HM
    apply Hlc; apply Hhead
  | mutable M _ _ _ _ HM Hlc Hmut =>
    rw [ctx_comp B M]
    constructor; apply step_lvl.mutable
    apply ctx𝕄.cons𝔹; apply HB; apply HM
    apply Hlc; apply Hmut
  | reflect P E _ _ HP HE Hlc =>
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

lemma step.congruence_under_ctxℝ :
  ∀ intro lvl R σ₀ σ₁ e₀ e₁,
    ctxℝ intro lvl R →
    step_lvl (lvl + intro) ⟨σ₀, e₀⟩ ⟨σ₁, e₁⟩ →
    step_lvl lvl ⟨σ₀, R⟦e₀⟧⟩ ⟨σ₁, R⟦e₁⟧⟩ :=
  by
  intros intro lvl R σ₀ σ₁ e₀ e₁ HR Hstep
  cases Hstep with
  | pure M _ _ _ HM Hlc Hhead =>
    repeat rw [ctx_comp R M]
    apply step_lvl.pure
    apply ctx𝕄.consℝ; apply HR; apply HM
    apply Hlc; apply Hhead
  | mutable M _ _ _ _ HM Hlc Hmut =>
    repeat rw [ctx_comp R M]
    apply step_lvl.mutable
    apply ctx𝕄.consℝ; apply HR; apply HM
    apply Hlc; apply Hmut
  | reflect P _ _ _ HP HE Hlc =>
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
