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
    ∃ v𝕖 i j,
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
      exists e₀, 0, k + 1
      constructor; omega
      constructor; apply Hvalue
      constructor; apply pure_stepn_indexed.refl
      apply pure_stepn_indexed.multi; apply Hstep; apply Hstepn
    | isFalse HNv =>
      have ⟨e₁, HEqe₁, Hstep₀⟩ := pure_step.refine _ _ _ HB HNv Hstep
      have ⟨v𝕖, i, j, HEqk, Hvalue, Hstep₁, Hstep₂⟩ := IH _ HEqe₁ Hvalue
      exists v𝕖, i + 1, j
      constructor; omega
      constructor; apply Hvalue
      constructor; apply pure_stepn_indexed.multi
      apply Hstep₀; apply Hstep₁; apply Hstep₂
