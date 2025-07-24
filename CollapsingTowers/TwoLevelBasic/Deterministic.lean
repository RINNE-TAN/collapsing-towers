
import CollapsingTowers.TwoLevelBasic.SmallStep
@[pp_using_anonymous_constructor]
structure HeadStepable (e : Expr) where
  mk ::
  Hlc : lc e
  HNv : ¬value e
  HAtomic𝔹 : ∀ B r, ctx𝔹 B → ¬value r → lc r → e ≠ B⟦r⟧
  HAtomicℝ : ∀ R r, ctxℝ intro lvl R → ¬value r → lc r → e ≠ R⟦r⟧

theorem head𝕄_impl_HeadStepable :
  ∀ e₀ e₁, lc e₀ → head𝕄 e₀ e₁ → HeadStepable e₀ :=
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
      rw [← open_close_id 0 r lvl, ← HEq]
      apply value.code
      rw [lc, open_lc]; apply Hlc
      apply Hlcr
    case let𝕔.let𝕔 =>
      rw [← open_close_id 0 r lvl, ← HEq.right]
      apply value.code
      rw [lc, open_lc]; apply Hlc.right
      apply Hlcr
    case run.run =>
      rw [← HEq]
      apply value.code
      apply Hlc

theorem reflect_impl_HeadStepable :
  ∀ b, lc b → HeadStepable (.reflect b) :=
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

theorem decompose𝔹_deterministic :
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

theorem decomposeℝ_deterministic :
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
    rw [← open_close_id _ _ _ Hlc₀, ← open_close_id _ _ _ Hlc₁]
    rw [HEq]
  case let𝕔.let𝕔 =>
    rw [← open_close_id _ _ _ Hlc₀, ← open_close_id _ _ _ Hlc₁]
    rw [← HEq.right]

theorem decompose𝔹_decomposeℝ_deterministic :
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

theorem ctx𝔹_not_value : ∀ B e, ctx𝔹 B → ¬value B⟦e⟧ :=
  by
  intros B e HB Hvalue
  cases HB <;> nomatch Hvalue

theorem ctxℝ_not_value : ∀ intro lvl R e, ctxℝ intro lvl R → ¬value R⟦e⟧ :=
  by
  intros intro lvl R e HR Hvalue
  cases HR <;> nomatch Hvalue

theorem ctx𝕄_not_value : ∀ lvl M e, ¬value e → ctx𝕄 lvl M → ¬value M⟦e⟧ :=
  by
  intros lvl M e HNv HM Hvalue
  cases HM
  case hole => apply HNv; apply Hvalue
  case cons𝔹 HB _ => apply ctx𝔹_not_value; apply HB; apply Hvalue
  case consℝ HR _ => apply ctxℝ_not_value; apply HR; apply Hvalue

theorem ctx𝕄_value_id : ∀ lvl M e, ctx𝕄 lvl M → value M⟦e⟧ → M = id :=
  by
  intros lvl M e HM Hvalue
  cases HM
  case hole => rfl
  case cons𝔹 HB _ => exfalso; apply ctx𝔹_not_value; apply HB; apply Hvalue
  case consℝ HR _ => exfalso; apply ctxℝ_not_value; apply HR; apply Hvalue

theorem decompose𝕄_deterministic :
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
      apply He₀.HAtomic𝔹
      apply HB₁; apply ctx𝕄_not_value _ _ _ He₁.HNv HM₁
      apply lc_ctx𝕄; apply HM₁; apply He₁.Hlc
      apply HEq
    case consℝ R₁ M₁ HR₁ HM₁ =>
      exfalso
      apply He₀.HAtomicℝ
      apply HR₁; apply ctx𝕄_not_value _ _ _ He₁.HNv HM₁
      apply lc_ctx𝕄; apply HM₁; apply He₁.Hlc
      apply HEq
  case cons𝔹 B₀ M₀ HB₀ HM₀ IH =>
    cases HM₁
    case hole =>
      exfalso
      apply He₁.HAtomic𝔹
      apply HB₀; apply ctx𝕄_not_value _ _ _ He₀.HNv HM₀
      apply lc_ctx𝕄; apply HM₀; apply He₀.Hlc
      symm; apply HEq
    case cons𝔹 B₁ M₁ HB₁ HM₁ =>
      have HNvM₀ := ctx𝕄_not_value _ _ _ He₀.HNv HM₀
      have HNvM₁ := ctx𝕄_not_value _ _ _ He₁.HNv HM₁
      have ⟨HEqM, HEqB⟩ := decompose𝔹_deterministic _ _ _ _ HB₀ HB₁ HEq HNvM₀ HNvM₁
      have ⟨HEqe, HEqM⟩ := IH _ HM₁ HEqM
      simp [HEqe, HEqB, HEqM]
    case consℝ R₁ M₁ HR₁ HM₁ =>
      exfalso
      apply decompose𝔹_decomposeℝ_deterministic
      apply HB₀; apply HR₁; apply HEq
      apply ctx𝕄_not_value _ _ _ He₀.HNv HM₀
      apply ctx𝕄_not_value _ _ _ He₁.HNv HM₁
  case consℝ R₀ M₀ HR₀ HM₀ IH =>
    cases HM₁
    case hole =>
      exfalso
      apply He₁.HAtomicℝ
      apply HR₀; apply ctx𝕄_not_value _ _ _ He₀.HNv HM₀
      apply lc_ctx𝕄; apply HM₀; apply He₀.Hlc
      symm; apply HEq
    case cons𝔹 B₁ M₁ HB₁ HM₁ =>
      exfalso
      apply decompose𝔹_decomposeℝ_deterministic
      apply HB₁; apply HR₀; symm; apply HEq
      apply ctx𝕄_not_value _ _ _ He₁.HNv HM₁
      apply ctx𝕄_not_value _ _ _ He₀.HNv HM₀
    case consℝ R₁ M₁ HR₁ HM₁ =>
      have HNvM₀ := ctx𝕄_not_value _ _ _ He₀.HNv HM₀
      have HNvM₁ := ctx𝕄_not_value _ _ _ He₁.HNv HM₁
      have Hlc₀ := lc_ctx𝕄 _ _ _ _ HM₀ He₀.Hlc
      have Hlc₁ := lc_ctx𝕄 _ _ _ _ HM₁ He₁.Hlc
      have ⟨HEqM, HEqi, HEqR⟩ := decomposeℝ_deterministic _ _ _ _ _ _ _ HR₀ HR₁ HEq Hlc₀ Hlc₁ HNvM₀ HNvM₁
      rw [HEqi] at IH
      have ⟨HEqe, HEqM⟩ := IH _ HM₁ HEqM
      simp [HEqe, HEqR, HEqM]

theorem head𝕄_deterministic :
  ∀ e l r,
    head𝕄 e l →
    head𝕄 e r →
    l = r :=
  by
  intros e l r Hstepl Hstepr
  cases Hstepl <;> cases Hstepr <;> rfl

theorem deterministic :
  ∀ e l r,
    step e l →
    step e r →
    l = r :=
  by
  intros e l r Hstepl Hstepr
  cases Hstepl
  case step𝕄 Ml el₀ el₁ HMl Hlcl Hheadl =>
    generalize HEq : Ml⟦el₀⟧ = e
    rw [HEq] at Hstepr
    cases Hstepr
    case step𝕄 Mr er₀ er₁ HMr Hlcr Hheadr =>
      have Hstepablel := head𝕄_impl_HeadStepable _ _ Hlcl Hheadl
      have Hstepabler := head𝕄_impl_HeadStepable _ _ Hlcr Hheadr
      have ⟨HEqe, HEqM⟩ := decompose𝕄_deterministic _ _ _ _ _ HMl HMr HEq Hstepablel Hstepabler
      rw [HEqe] at Hheadl
      have HEqr := head𝕄_deterministic _ _ _ Hheadl Hheadr
      rw [HEqM, HEqr]
    case reflect Pr Er br HPr HEr Hlcr =>
      exfalso
      have HMr : ctx𝕄 0 (Pr ∘ Er) :=
        by
        apply compose_ctx𝕄_ctx𝔼
        apply rewrite_ctxℙ_to_ctx𝕄
        apply HPr; apply HEr
      have Hstepablel := head𝕄_impl_HeadStepable _ _ Hlcl Hheadl
      have Hstepabler := reflect_impl_HeadStepable _ Hlcr
      have ⟨HEqe, HEqM⟩ := decompose𝕄_deterministic _ _ _ _ _ HMl HMr HEq Hstepablel Hstepabler
      rw [HEqe] at Hheadl
      nomatch Hheadl
  case reflect Pl El bl HPl HEl Hlcl =>
    generalize HEq : Pl⟦El⟦.reflect bl⟧⟧ = e
    rw [HEq] at Hstepr
    cases Hstepr
    case step𝕄 Mr er₀ er₁ HMr Hlcr Hheadr =>
      exfalso
      have HMl : ctx𝕄 0 (Pl ∘ El) :=
        by
        apply compose_ctx𝕄_ctx𝔼
        apply rewrite_ctxℙ_to_ctx𝕄
        apply HPl; apply HEl
      have Hstepablel := reflect_impl_HeadStepable _ Hlcl
      have Hstepabler := head𝕄_impl_HeadStepable _ _ Hlcr Hheadr
      have ⟨HEqe, HEqM⟩ := decompose𝕄_deterministic _ _ _ _ _ HMl HMr HEq Hstepablel Hstepabler
      rw [← HEqe] at Hheadr
      nomatch Hheadr
    case reflect Pr Er br HPr HEr Hlcr =>
      admit

theorem church_rosser_strengthened :
  ∀ e₀ l r,
    stepn e₀ l →
    stepn e₀ r →
    ∃ v,
      stepn l v ∧
      stepn r v :=
  by
  intros e₀ l r Hstepl Hstepr
  induction Hstepl generalizing r
  case refl =>
    exists r; constructor
    . apply Hstepr
    . apply stepn.refl
  case multi le₀ le₁ le₂ IHstepl IHstepln IH =>
    cases Hstepr
    case refl =>
      exists le₂; constructor
      . apply stepn.refl
      . apply stepn.multi; apply IHstepl; apply IHstepln
    case multi re₀ IHstepr IHsteprn =>
      apply IH
      rw [deterministic _ _ _ IHstepl IHstepr]
      apply IHsteprn

theorem value_termination : ∀ v e, value v → ¬step v e :=
  by
  intros v e Hvalue Hstep
  cases Hstep
  case step𝕄 HM _ Hhead =>
    rw [ctx𝕄_value_id _ _ _ HM Hvalue] at Hvalue
    cases Hhead <;> nomatch Hvalue
  case reflect P E _ HP HE _ =>
    have HM : ctx𝕄 0 (P ∘ E) :=
      by
      apply compose_ctx𝕄_ctx𝔼
      apply rewrite_ctxℙ_to_ctx𝕄
      apply HP; apply HE
    rw [ctx_comp P E, ctx𝕄_value_id _ _ _ HM Hvalue] at Hvalue
    nomatch Hvalue

theorem church_rosser :
  ∀ e v₀ v₁,
    stepn e v₀ →
    stepn e v₁ →
    value v₀ →
    value v₁ →
    v₀ = v₁ :=
  by
  intros e v₀ v₁ Hstep₀ Hstep₁ Hvalue₀ Hvalue₁
  have ⟨v, Hstep₀, Hstep₁⟩ := church_rosser_strengthened _ _ _ Hstep₀ Hstep₁
  cases Hstep₀
  case refl =>
    cases Hstep₁
    case refl => rfl
    case multi Hstep _ =>
      exfalso; apply value_termination
      apply Hvalue₁; apply Hstep
  case multi Hstep _ =>
    exfalso; apply value_termination
    apply Hvalue₀; apply Hstep
