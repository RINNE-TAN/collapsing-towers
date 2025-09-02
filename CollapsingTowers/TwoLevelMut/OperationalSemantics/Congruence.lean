import CollapsingTowers.TwoLevelMut.OperationalSemantics.SmallStep

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
