import CollapsingTowers.TwoLvLBasic.Semantic.SmallStep
@[pp_using_anonymous_constructor]
structure HeadStepable (e : Expr) where
  mk ::
  Hlc : lc e
  HNv : ¬value e
  HAtomic𝔹 : ∀ B r, ctx𝔹 B → ¬value r → lc r → e ≠ B⟦r⟧
  HAtomicℝ : ∀ R r, ctxℝ intro lvl R → ¬value r → lc r → e ≠ R⟦r⟧

lemma head_impl_head_stepable : ∀ e₀ e₁, lc e₀ → head e₀ e₁ → HeadStepable e₀ :=
  by
  intros e₀ e₁ Hlc Hhead
  apply HeadStepable.mk
  case Hlc =>
    apply Hlc
  case HNv =>
    intros Hvalue
    cases Hhead <;> nomatch Hvalue
  case HAtomic𝔹 =>
    intros B r HB HNv _ HEq
    apply HNv
    cases Hhead <;> cases HB <;> simp at HEq <;> simp [← HEq]
    case lets.lets => assumption
    case app₁.appl₁ =>
      apply value.lam
      apply Hlc.left
    case app₁.appr₁ => assumption
    case app₂.appl₂ =>
      apply value.code
      apply Hlc.left
    case app₂.appr₂ =>
      apply value.code
      apply Hlc.right
    case lift_lit.lift =>
      apply value.lit
    case lift_lam.lift =>
      apply value.lam
      apply Hlc
  case HAtomicℝ =>
    intros _ lvl R r HR HNv Hlcr HEq
    apply HNv
    cases Hhead <;> cases HR <;> simp at HEq
    case lam𝕔.lam𝕔 =>
      rw [← identity.opening_closing 0 r lvl, ← HEq]
      apply value.code
      simp [lc.under_opening]; apply Hlc
      apply Hlcr
    case let𝕔.let𝕔 =>
      rw [← identity.opening_closing 0 r lvl, ← HEq.right]
      apply value.code
      simp [lc.under_opening]; apply Hlc.right
      apply Hlcr
    case run.run =>
      rw [← HEq]
      apply value.code
      apply Hlc

lemma reflect_impl_head_stepable : ∀ b, lc b → HeadStepable (.reflect b) :=
  by
  intros b Hlc
  apply HeadStepable.mk
  case Hlc => apply Hlc
  case HNv => intro HValue; nomatch HValue
  case HAtomic𝔹 =>
    intros _ _ HB _ _ HEq
    cases HB <;> simp at HEq
  case HAtomicℝ =>
    intros _ _ R _ HR _ _ HEq
    cases HR <;> simp at HEq

lemma not_value.under_ctx𝔹 : ∀ B e, ctx𝔹 B → ¬value B⟦e⟧ :=
  by
  intros B e HB Hvalue
  cases HB <;> nomatch Hvalue

lemma not_value.under_ctxℝ : ∀ intro lvl R e, ctxℝ intro lvl R → ¬value R⟦e⟧ :=
  by
  intros intro lvl R e HR Hvalue
  cases HR <;> nomatch Hvalue

lemma not_value.under_ctx𝔼 : ∀ E e, ¬value e → ctx𝔼 E → ¬value E⟦e⟧ :=
  by
  intros E e HNv HE Hvalue
  cases HE
  case hole => apply HNv; apply Hvalue
  case cons𝔹 HB _ => apply not_value.under_ctx𝔹; apply HB; apply Hvalue

lemma not_value.under_ctx𝕄 : ∀ lvl M e, ¬value e → ctx𝕄 lvl M → ¬value M⟦e⟧ :=
  by
  intros lvl M e HNv HM Hvalue
  cases HM
  case hole => apply HNv; apply Hvalue
  case cons𝔹 HB _ => apply not_value.under_ctx𝔹; apply HB; apply Hvalue
  case consℝ HR _ => apply not_value.under_ctxℝ; apply HR; apply Hvalue

lemma not_value.under_ctxℚ : ∀ lvl Q e, ctxℚ lvl Q → ¬value Q⟦e⟧ :=
  by
  intros lvl Q e HQ Hvalue
  cases HQ
  case holeℝ HR => apply not_value.under_ctxℝ; apply HR; apply Hvalue
  case cons𝔹 HB _ => apply not_value.under_ctx𝔹; apply HB; apply Hvalue
  case consℝ HR _ => apply not_value.under_ctxℝ; apply HR; apply Hvalue

theorem deterministic.head :
  ∀ e l r,
    head e l →
    head e r →
    l = r :=
  by
  intros e l r Hstepl Hstepr
  cases Hstepl <;> cases Hstepr <;> rfl

lemma deterministic.under_ctx𝔹 :
  ∀ e₀ e₁ B₀ B₁,
    ctx𝔹 B₀ →
    ctx𝔹 B₁ →
    B₀⟦e₀⟧ = B₁⟦e₁⟧ →
    ¬value e₀ →
    ¬value e₁ →
    e₀ = e₁ ∧ B₀ = B₁ :=
  by
  intros e₀ e₁ B₀ B₁ HB₀ HB₁ HEq HNv₀ HNv₁
  cases HB₀ <;>
  cases HB₁ <;>
  (simp at HEq; try simp [HEq]) <;>
  exfalso <;>
  (try apply HNv₀; simp [HEq]; assumption) <;>
  (try apply HNv₁; simp [← HEq]; assumption)

lemma deterministic.under_ctxℝ :
  ∀ e₀ e₁ lvl intro₀ intro₁ R₀ R₁,
    ctxℝ intro₀ lvl R₀ →
    ctxℝ intro₁ lvl R₁ →
    R₀⟦e₀⟧ = R₁⟦e₁⟧ →
    lc e₀ →
    lc e₁ →
    ¬value e₀ →
    ¬value e₁ →
    e₀ = e₁ ∧ intro₀ = intro₁ ∧ R₀ = R₁ :=
  by
  intros e₀ e₁ lvl intro₀ intro₁ R₀ R₁ HR₀ HR₁ HEq Hlc₀ Hlc₁ HNv₀ HNv₁
  cases HR₀ <;>
  cases HR₁ <;>
  (simp at HEq; try simp [HEq])
  case lam𝕔.lam𝕔 =>
    rw [← identity.opening_closing _ _ _ Hlc₀]
    rw [← identity.opening_closing _ _ _ Hlc₁]
    rw [HEq]
  case let𝕔.let𝕔 =>
    rw [← identity.opening_closing _ _ _ Hlc₀]
    rw [← identity.opening_closing _ _ _ Hlc₁]
    rw [← HEq.right]

lemma deterministic.under_ctx𝔹_ctxℝ :
  ∀ e₀ e₁ lvl intro B R,
    ctx𝔹 B →
    ctxℝ intro lvl R →
    B⟦e₀⟧ = R⟦e₁⟧ →
    ¬value e₀ →
    ¬value e₁ →
    False :=
  by
  intros e₀ e₁ lvl intro B R HB HR HEq HNv₀ HNv₁
  cases HB <;> cases HR <;> nomatch HEq

theorem deterministic.under_ctx𝕄 :
  ∀ e₀ e₁ lvl M₀ M₁,
    ctx𝕄 lvl M₀ →
    ctx𝕄 lvl M₁ →
    M₀⟦e₀⟧ = M₁⟦e₁⟧ →
    HeadStepable e₀ →
    HeadStepable e₁ →
    e₀ = e₁ ∧ M₀ = M₁ :=
  by
  intros e₀ e₁ lvl M₀ M₁ HM₀ HM₁ HEq He₀ He₁
  induction HM₀ generalizing M₁
  case hole =>
    cases HM₁
    case hole => simp; apply HEq
    case cons𝔹 B₁ M₁ HB₁ HM₁ =>
      exfalso
      apply He₀.HAtomic𝔹; apply HB₁
      apply not_value.under_ctx𝕄 _ _ _ He₁.HNv HM₁
      apply lc.under_ctx𝕄; apply HM₁; apply He₁.Hlc
      apply HEq
    case consℝ R₁ M₁ HR₁ HM₁ =>
      exfalso
      apply He₀.HAtomicℝ; apply HR₁
      apply not_value.under_ctx𝕄 _ _ _ He₁.HNv HM₁
      apply lc.under_ctx𝕄; apply HM₁; apply He₁.Hlc
      apply HEq
  case cons𝔹 B₀ M₀ HB₀ HM₀ IH =>
    cases HM₁
    case hole =>
      exfalso
      apply He₁.HAtomic𝔹; apply HB₀
      apply not_value.under_ctx𝕄 _ _ _ He₀.HNv HM₀
      apply lc.under_ctx𝕄; apply HM₀; apply He₀.Hlc
      symm; apply HEq
    case cons𝔹 B₁ M₁ HB₁ HM₁ =>
      have HNvM₀ := not_value.under_ctx𝕄 _ _ _ He₀.HNv HM₀
      have HNvM₁ := not_value.under_ctx𝕄 _ _ _ He₁.HNv HM₁
      have ⟨HEqM, HEqB⟩ := deterministic.under_ctx𝔹 _ _ _ _ HB₀ HB₁ HEq HNvM₀ HNvM₁
      have ⟨HEqe, HEqM⟩ := IH _ HM₁ HEqM
      simp [HEqe, HEqB, HEqM]
    case consℝ R₁ M₁ HR₁ HM₁ =>
      exfalso
      apply deterministic.under_ctx𝔹_ctxℝ
      apply HB₀; apply HR₁; apply HEq
      apply not_value.under_ctx𝕄 _ _ _ He₀.HNv HM₀
      apply not_value.under_ctx𝕄 _ _ _ He₁.HNv HM₁
  case consℝ R₀ M₀ HR₀ HM₀ IH =>
    cases HM₁
    case hole =>
      exfalso
      apply He₁.HAtomicℝ; apply HR₀
      apply not_value.under_ctx𝕄 _ _ _ He₀.HNv HM₀
      apply lc.under_ctx𝕄; apply HM₀; apply He₀.Hlc
      symm; apply HEq
    case cons𝔹 B₁ M₁ HB₁ HM₁ =>
      exfalso
      apply deterministic.under_ctx𝔹_ctxℝ
      apply HB₁; apply HR₀; symm; apply HEq
      apply not_value.under_ctx𝕄 _ _ _ He₁.HNv HM₁
      apply not_value.under_ctx𝕄 _ _ _ He₀.HNv HM₀
    case consℝ R₁ M₁ HR₁ HM₁ =>
      have HNvM₀ := not_value.under_ctx𝕄 _ _ _ He₀.HNv HM₀
      have HNvM₁ := not_value.under_ctx𝕄 _ _ _ He₁.HNv HM₁
      have Hlc₀ := lc.under_ctx𝕄 _ _ _ _ HM₀ He₀.Hlc
      have Hlc₁ := lc.under_ctx𝕄 _ _ _ _ HM₁ He₁.Hlc
      have ⟨HEqM, HEqi, HEqR⟩ := deterministic.under_ctxℝ _ _ _ _ _ _ _ HR₀ HR₁ HEq Hlc₀ Hlc₁ HNvM₀ HNvM₁
      rw [HEqi] at IH
      have ⟨HEqe, HEqM⟩ := IH _ HM₁ HEqM
      simp [HEqe, HEqR, HEqM]
