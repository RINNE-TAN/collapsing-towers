import CollapsingTowers.TwoLevelRec.Semantic.Deterministic

-- B⟦e₀⟧ ⇾ r
-- ———————————————————————
-- B⟦e₀⟧ ⇾ B⟦e₁⟧ ∧ e₀ ⇾ e₁
lemma pure_step.refine :
  ∀ B₀ e₀ r,
    ctx𝔹 B₀ →
    ¬value e₀ →
    (B₀⟦e₀⟧ ⇾ r) →
    ∃ e₁, B₀⟦e₁⟧ = r ∧ (e₀ ⇾ e₁) :=
  by
  intros B₀ e₀ r HB₀ HNv
  generalize HEqe : B₀⟦e₀⟧ = E₀
  intros Hstep
  cases Hstep
  case pure M e₁ e₂ HM Hlc Hhead =>
    have Hstepable := head_impl_head_stepable _ _ Hlc Hhead
    cases HM
    case hole =>
      exfalso
      apply Hstepable.HAtomic𝔹
      apply HB₀; apply HNv
      symm; apply HEqe
    case cons𝔹 B₁ M HB₁ HM =>
      have HNvM₁ := not_value.under_ctx𝕄 _ _ _ Hstepable.HNv HM
      have ⟨HEqM, HEqB⟩ := deterministic.under_ctx𝔹 _ _ _ _ HB₀ HB₁ HEqe HNv HNvM₁
      exists M⟦e₂⟧
      constructor; simp [HEqB]
      rw [HEqM]; apply pure_step.pure
      apply HM; apply Hlc; apply Hhead
    case consℝ HR HM =>
      exfalso
      apply deterministic.under_ctx𝔹_ctxℝ
      apply HB₀; apply HR; apply HEqe
      apply HNv; apply not_value.under_ctx𝕄
      apply Hstepable.HNv; apply HM

-- B⟦e⟧ ⇾ₖ v
-- —————————————————————————————————
-- k = i + j ∧ e ⇾ᵢ v𝕖 ∧ B⟦v𝕖⟧ ⇾ⱼ v
lemma pure_stepn_indexed.refine :
  ∀ B e₀ v k,
    ctx𝔹 B →
    value v →
    (B⟦e₀⟧ ⇾ ⟦k⟧ v) →
    ∃ i j v𝕖,
      i + j = k ∧
      value v𝕖 ∧
      (e₀ ⇾ ⟦i⟧ v𝕖) ∧
      (B⟦v𝕖⟧ ⇾ ⟦j⟧ v) :=
  by
  intros B e₀ v k HB
  generalize HEqe₀ : B⟦e₀⟧ = E
  intros Hvalue Hstep
  induction Hstep generalizing e₀
  case refl =>
    exfalso; apply not_value.under_ctx𝔹
    apply HB; rw [HEqe₀]; apply Hvalue
  case multi k im₀ im₁ im₂ Hstep Hstepn IH =>
    rw [← HEqe₀] at Hstep
    match value.decidable e₀ with
    | isTrue Hvalue =>
      exists 0, k + 1, e₀
      constructor; omega
      constructor; apply Hvalue
      constructor; apply pure_stepn_indexed.refl
      apply pure_stepn_indexed.multi; apply Hstep; apply Hstepn
    | isFalse HNv =>
      have ⟨e₁, HEqe₁, Hstep₀⟩ := pure_step.refine _ _ _ HB HNv Hstep
      have ⟨i, j, v𝕖, HEqk, Hvalue, Hstep₁, Hstep₂⟩ := IH _ HEqe₁ Hvalue
      exists i + 1, j, v𝕖
      constructor; omega
      constructor; apply Hvalue
      constructor; apply pure_stepn_indexed.multi
      apply Hstep₀; apply Hstep₁; apply Hstep₂

lemma pure_stepn_indexed.refine.app₁ :
  ∀ f arg v j,
    value v →
    ((.app₁ f arg) ⇾ ⟦j⟧ v) →
    ∃ i₀ i₁ i₂ fᵥ argᵥ,
      i₀ + i₁ + i₂ = j ∧
      value fᵥ ∧ value argᵥ ∧
      (f ⇾ ⟦i₀⟧ fᵥ) ∧ (arg ⇾ ⟦i₁⟧ argᵥ) ∧ ((.app₁ fᵥ argᵥ) ⇾ ⟦i₂⟧ v) :=
  by
  intros f arg v j Hvalue Hstep
  have Hlc := lc.under_pure_stepn_indexed _ _ _ Hstep (lc.value _ Hvalue)
  have ⟨i₀, k, fᵥ, HEqj, HvalueF, Hstep₀, Hstep⟩ := pure_stepn_indexed.refine _ _ _ _ (ctx𝔹.appl₁ _ Hlc.right) Hvalue Hstep
  have ⟨i₁, i₂, argᵥ, HEqj, HvalueArg, Hstep₁, Hstep₂⟩ := pure_stepn_indexed.refine _ _ _ _ (ctx𝔹.appr₁ _ HvalueF) Hvalue Hstep
  exists i₀, i₁, i₂, fᵥ, argᵥ
  constructor; omega
  constructor; apply HvalueF
  constructor; apply HvalueArg
  constructor; apply Hstep₀
  constructor; apply Hstep₁
  apply Hstep₂

lemma pure_stepn_indexed.refine.lets :
  ∀ b e v j,
    value v →
    ((.lets b e) ⇾ ⟦j⟧ v) →
    ∃ i₀ i₁ bᵥ,
      i₀ + i₁ = j ∧
      value bᵥ ∧
      (b ⇾ ⟦i₀⟧ bᵥ) ∧ ((.lets bᵥ e) ⇾ ⟦i₁⟧ v) :=
  by
  intros b e v j Hvalue Hstep
  have Hlc := lc.under_pure_stepn_indexed _ _ _ Hstep (lc.value _ Hvalue)
  apply pure_stepn_indexed.refine
  apply ctx𝔹.lets; apply Hlc.right
  apply Hvalue; apply Hstep
