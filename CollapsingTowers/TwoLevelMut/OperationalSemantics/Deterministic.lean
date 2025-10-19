import CollapsingTowers.TwoLevelMut.OperationalSemantics.SmallStep

@[pp_using_anonymous_constructor]
structure HeadStepable (e : Expr) where
  mk ::
  Hlc : lc e
  HNv : ¬value e
  HAtomic𝔹 : ∀ B r, ctx𝔹 B → ¬value r → e ≠ B⟦r⟧
  HAtomicℝ : ∀ R r, ctxℝ intro lvl R → ¬value r → lc r → e ≠ R⟦r⟧

lemma head_pure_impl_head_stepable : ∀ e₀ e₁, lc e₀ → head_pure e₀ e₁ → HeadStepable e₀ :=
  by
  intros e₀ e₁ Hlc Hhead
  apply HeadStepable.mk
  case Hlc =>
    apply Hlc
  case HNv =>
    intros Hvalue
    cases Hhead <;> nomatch Hvalue
  case HAtomic𝔹 =>
    intros B r HB HNv HEq
    apply HNv
    cases Hhead <;> cases HB <;> simp at HEq <;> simp [← HEq]
    case lets.lets => assumption
    case app₁.appl₁ => apply value.lam; apply Hlc.left
    case app₁.appr₁ => assumption
    case app₂.appl₂ => apply value.code; apply Hlc.left
    case app₂.appr₂ => apply value.code; apply Hlc.right
    case lift_lit.lift => apply value.lit
    case lift_lam.lift => apply value.lam; apply Hlc
    case lift_unit.lift => apply value.unit
    case load₂.load₂ => apply value.code; apply Hlc
    case alloc₂.alloc₂ => apply value.code; apply Hlc
    case store₂.storel₂ => apply value.code; apply Hlc.left
    case store₂.storer₂ => apply value.code; apply Hlc.right
  case HAtomicℝ =>
    intros _ lvl R r HR HNv Hlcr HEq
    apply HNv
    cases Hhead <;> cases HR <;> simp at HEq
    case lam𝕔.lam𝕔 =>
      rw [← identity.opening_closing 0 r lvl, ← HEq]
      apply value.code
      simp [lc.under_opening]; apply Hlc
      apply Hlcr
    case lets𝕔.lets𝕔 =>
      rw [← identity.opening_closing 0 r lvl, ← HEq.right]
      apply value.code
      simp [lc.under_opening]; apply Hlc.right
      apply Hlcr
    case run.run => rw [← HEq]; apply value.code; apply Hlc

lemma head_mutable_impl_head_stepable : ∀ σ₀ σ₁ e₀ e₁, lc e₀ → head_mutable ⟨σ₀, e₀⟩ ⟨σ₁, e₁⟩ → HeadStepable e₀ :=
  by
  intros σ₀ σ₁ e₀ e₁ Hlc Hmut
  apply HeadStepable.mk
  case Hlc =>
    apply Hlc
  case HNv =>
    intros Hvalue
    cases Hmut <;> nomatch Hvalue
  case HAtomic𝔹 =>
    intros B r HB HNv HEq
    apply HNv
    cases Hmut <;> cases HB <;> simp at HEq <;> simp [← HEq]
    case alloc₁.alloc₁ => apply value.lit
    case load₁.load₁ => apply value.loc
    case store₁.storel₁ => apply value.loc
    case store₁.storer₁ => apply value.lit
  case HAtomicℝ =>
    intros _ lvl R r HR HNv Hlcr HEq
    cases Hmut <;> cases HR <;> simp at HEq

lemma reflect_impl_head_stepable : ∀ b, lc b → HeadStepable (.reflect b) :=
  by
  intros b Hlc
  apply HeadStepable.mk
  case Hlc => apply Hlc
  case HNv => intro HValue; nomatch HValue
  case HAtomic𝔹 =>
    intros _ _ HB _ HEq
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

lemma deterministic.head_pure :
  ∀ e l r,
    head_pure e l →
    head_pure e r →
    l = r :=
  by
  intros e l r Hstepl Hstepr
  cases Hstepl <;> cases Hstepr <;> rfl

theorem deterministic.head_mutable :
  ∀ σ σl σr e l r,
    head_mutable ⟨σ, e⟩ ⟨σl, l⟩ →
    head_mutable ⟨σ, e⟩ ⟨σr, r⟩ →
    σl = σr ∧ l = r :=
  by
  intros σ σl σr e l r Hmutl Hmutr
  cases Hmutl <;> cases Hmutr
  case alloc₁.alloc₁ => simp
  case load₁.load₁ l n₀ Hbinds₀ n₁ Hbinds₁ =>
    simp at Hbinds₀ Hbinds₁
    simp [Hbinds₀] at Hbinds₁
    simp [Hbinds₁]
  case store₁.store₁ l n Hpatch₀ Hpatch₁ =>
    simp at Hpatch₀ Hpatch₁
    simp [Hpatch₀] at Hpatch₁
    simp [Hpatch₁]

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
  case lets𝕔.lets𝕔 =>
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
  cases HB <;> cases HR <;> try simp at HEq

lemma deterministic.under_ctx𝔼 :
  ∀ e₀ e₁ E₀ E₁,
    ctx𝔼 E₀ →
    ctx𝔼 E₁ →
    E₀⟦e₀⟧ = E₁⟦e₁⟧ →
    HeadStepable e₀ →
    HeadStepable e₁ →
    e₀ = e₁ ∧ E₀ = E₁ :=
  by
  intros e₀ e₁ E₀ E₁ HE₀ HE₁ HEq He₀ He₁
  induction HE₀ generalizing E₁
  case hole =>
    cases HE₁
    case hole => simp; apply HEq
    case cons𝔹 B₁ E₁ HB₁ HE₁ =>
      exfalso
      apply He₀.HAtomic𝔹; apply HB₁
      apply not_value.under_ctx𝔼 _ _ He₁.HNv HE₁
      apply HEq
  case cons𝔹 B₀ E₀ HB₀ HE₀ IH =>
    cases HE₁
    case hole =>
      exfalso
      apply He₁.HAtomic𝔹; apply HB₀
      apply not_value.under_ctx𝔼 _ _ He₀.HNv HE₀
      symm; apply HEq
    case cons𝔹 B₁ E₁ HB₁ HE₁ =>
      have HNvM₀ := not_value.under_ctx𝔼 _ _ He₀.HNv HE₀
      have HNvM₁ := not_value.under_ctx𝔼 _ _ He₁.HNv HE₁
      have ⟨HEqM, HEqB⟩ := deterministic.under_ctx𝔹 _ _ _ _ HB₀ HB₁ HEq HNvM₀ HNvM₁
      have ⟨HEqe, HEqM⟩ := IH _ HE₁ HEqM
      simp [HEqe, HEqB, HEqM]

lemma deterministic.under_ctx𝕄 :
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

lemma deterministic.under_ctxℚ_ctx𝔼 :
  ∀ el er lvl Qr El Er,
    ctxℚ lvl Qr →
    ctx𝔼 El →
    ctx𝔼 Er →
    El⟦el⟧ = Qr⟦Er⟦er⟧⟧ →
    HeadStepable el →
    HeadStepable er →
    False :=
  by
  intros el er lvl Qr El Er HQr HEl HEr HEq Hel Her
  induction HQr generalizing El
  case holeℝ Rr HRr =>
    cases HEl
    case hole =>
      apply Hel.HAtomicℝ; apply HRr
      apply not_value.under_ctx𝔼
      apply Her.HNv; apply HEr
      apply lc.under_ctx𝔼 _ _ _ HEr
      apply Her.Hlc; apply HEq
    case cons𝔹 Bl El HBl HEl =>
      apply deterministic.under_ctx𝔹_ctxℝ
      apply HBl; apply HRr; apply HEq
      . apply not_value.under_ctx𝔼
        apply Hel.HNv; apply HEl
      . apply not_value.under_ctx𝔼
        apply Her.HNv; apply HEr
  case consℝ Rr Qr HRr HQr IH =>
    cases HEl
    case hole =>
      apply Hel.HAtomicℝ; apply HRr
      apply not_value.under_ctxℚ _ _ Er⟦er⟧
      apply HQr
      apply lc.under_ctxℚ _ _ _ _ HQr
      apply lc.under_ctx𝔼 _ _ _ HEr
      apply Her.Hlc; apply HEq
    case cons𝔹 Bl El HBl HEl =>
      apply deterministic.under_ctx𝔹_ctxℝ
      apply HBl; apply HRr; apply HEq
      . apply not_value.under_ctx𝔼
        apply Hel.HNv; apply HEl
      . apply not_value.under_ctxℚ _ _ Er⟦er⟧
        apply HQr
  case cons𝔹 lvl Br Qr HBr HQr IH =>
    cases HEl
    case hole =>
      apply Hel.HAtomic𝔹; apply HBr
      apply not_value.under_ctxℚ _ _ Er⟦er⟧
      apply HQr; apply HEq
    case cons𝔹 Bl El HBl HEl =>
      apply IH; apply HEl
      have HNvl : ¬value El⟦el⟧ :=
      by
       apply not_value.under_ctx𝔼
       apply Hel.HNv; apply HEl
      have HNvr : ¬value Qr⟦Er⟦er⟧⟧ :=
      by
        apply not_value.under_ctxℚ _ _ Er⟦er⟧
        apply HQr
      have ⟨HEqM, HEqB⟩ := deterministic.under_ctx𝔹 _ _ _ _ HBl HBr HEq HNvl HNvr
      apply HEqM

lemma deterministic.under_ctxℚ :
  ∀ el er lvl Ql Qr El Er,
    ctxℚ lvl Ql →
    ctxℚ lvl Qr →
    ctx𝔼 El →
    ctx𝔼 Er →
    Ql⟦El⟦el⟧⟧ = Qr⟦Er⟦er⟧⟧ →
    HeadStepable el →
    HeadStepable er →
    El⟦el⟧ = Er⟦er⟧ ∧ Ql = Qr :=
  by
  intros el er lvl Ql Qr El Er HQl HQr HEl HEr HEq Hel Her
  induction HQl generalizing Qr
  case holeℝ Rl HRl =>
    cases HQr
    case holeℝ HRr =>
      have HNvl := not_value.under_ctx𝔼 _ _ Hel.HNv HEl
      have HNvr := not_value.under_ctx𝔼 _ _ Her.HNv HEr
      have Hlcl := lc.under_ctx𝔼 _ _ _ HEl Hel.Hlc
      have Hlcr := lc.under_ctx𝔼 _ _ _ HEr Her.Hlc
      have ⟨HEqM, HEqi, HEqR⟩ := deterministic.under_ctxℝ _ _ _ _ _ _ _ HRl HRr HEq Hlcl Hlcr HNvl HNvr
      constructor
      apply HEqM; apply HEqR
    case cons𝔹 Br Qr HBr HQr =>
      exfalso
      apply deterministic.under_ctx𝔹_ctxℝ
      apply HBr; apply HRl
      symm; apply HEq
      . apply not_value.under_ctxℚ _ _ Er⟦er⟧
        apply HQr
      . apply not_value.under_ctx𝔼
        apply Hel.HNv; apply HEl
    case consℝ lvl intro Rr Qr HRr HQr =>
      exfalso
      have HNvl : ¬value El⟦el⟧ :=
      by
       apply not_value.under_ctx𝔼
       apply Hel.HNv; apply HEl
      have HNvr : ¬value Qr⟦Er⟦er⟧⟧ :=
      by
        apply not_value.under_ctxℚ _ _ Er⟦er⟧
        apply HQr
      have Hlcl := lc.under_ctx𝔼 _ _ _ HEl Hel.Hlc
      have Hlcr := lc.under_ctxℚ _ _ _ _ HQr (lc.under_ctx𝔼 _ _ _ HEr Her.Hlc)
      have ⟨HEqM, HEqi, HEqR⟩ := deterministic.under_ctxℝ _ _ _ _ _ _ _ HRl HRr HEq Hlcl Hlcr HNvl HNvr
      apply deterministic.under_ctxℚ_ctx𝔼
      apply HQr; apply HEl; apply HEr
      apply HEqM; apply Hel; apply Her
  case cons𝔹 Bl Ql HBl HQl IH =>
    cases HQr
    case holeℝ HRr =>
      exfalso
      apply deterministic.under_ctx𝔹_ctxℝ
      apply HBl; apply HRr
      apply HEq
      . apply not_value.under_ctxℚ _ _ El⟦el⟧
        apply HQl
      . apply not_value.under_ctx𝔼
        apply Her.HNv; apply HEr
    case cons𝔹 lvl Br Qr HBr HQr =>
      have HNvl : ¬value Ql⟦El⟦el⟧⟧ :=
      by
        apply not_value.under_ctxℚ _ _ El⟦el⟧
        apply HQl
      have HNvr : ¬value Qr⟦Er⟦er⟧⟧ :=
      by
        apply not_value.under_ctxℚ _ _ Er⟦er⟧
        apply HQr
      have ⟨HEqM, HEqB⟩ := deterministic.under_ctx𝔹 _ _ _ _ HBl HBr HEq HNvl HNvr
      have ⟨HEqe, HEqQ⟩ := IH _ HQr HEqM
      simp [HEqe, HEqB, HEqQ]
    case consℝ Rr Qr HRr HQr =>
      exfalso
      apply deterministic.under_ctx𝔹_ctxℝ
      apply HBl; apply HRr
      apply HEq
      . apply not_value.under_ctxℚ _ _ El⟦el⟧
        apply HQl
      . apply not_value.under_ctxℚ _ _ Er⟦er⟧
        apply HQr
  case consℝ introl lvl Rl Ql HRl HQl IH =>
    cases HQr
    case holeℝ HRr =>
      exfalso
      have HNvl : ¬value Ql⟦El⟦el⟧⟧ :=
      by
        apply not_value.under_ctxℚ _ _ El⟦el⟧
        apply HQl
      have HNvr : ¬value Er⟦er⟧ :=
      by
        apply not_value.under_ctx𝔼
        apply Her.HNv; apply HEr
      have Hlcl := lc.under_ctxℚ _ _ _ _ HQl (lc.under_ctx𝔼 _ _ _ HEl Hel.Hlc)
      have Hlcr := lc.under_ctx𝔼 _ _ _ HEr Her.Hlc
      have ⟨HEqM, HEqi, HEqR⟩ := deterministic.under_ctxℝ _ _ _ _ _ _ _ HRl HRr HEq Hlcl Hlcr HNvl HNvr
      apply deterministic.under_ctxℚ_ctx𝔼
      apply HQl; apply HEr; apply HEl
      symm; apply HEqM; apply Her; apply Hel
    case cons𝔹 lvl Br Qr HBr HQr =>
      exfalso
      apply deterministic.under_ctx𝔹_ctxℝ
      apply HBr; apply HRl
      symm; apply HEq
      . apply not_value.under_ctxℚ _ _ Er⟦er⟧
        apply HQr
      . apply not_value.under_ctxℚ _ _ El⟦el⟧
        apply HQl
    case consℝ intror Rr Qr HRr HQr =>
      have HNvl : ¬value Ql⟦El⟦el⟧⟧ :=
      by
        apply not_value.under_ctxℚ _ _ El⟦el⟧
        apply HQl
      have HNvr : ¬value Qr⟦Er⟦er⟧⟧ :=
      by
        apply not_value.under_ctxℚ _ _ Er⟦er⟧
        apply HQr
      have Hlcl := lc.under_ctxℚ _ _ _ _ HQl (lc.under_ctx𝔼 _ _ _ HEl Hel.Hlc)
      have Hlcr := lc.under_ctxℚ _ _ _ _ HQr (lc.under_ctx𝔼 _ _ _ HEr Her.Hlc)
      have ⟨HEqM, HEqi, HEqR⟩ := deterministic.under_ctxℝ _ _ _ _ _ _ _ HRl HRr HEq Hlcl Hlcr HNvl HNvr
      rw [← HEqi] at HQr
      have ⟨HEqe, HEqQ⟩ := IH _ HQr HEqM
      simp [HEqe, HEqR, HEqQ]

lemma deterministic.under_ctxℙ :
  ∀ el er lvl Pl Pr El Er,
    ctxℙ lvl Pl →
    ctxℙ lvl Pr →
    ctx𝔼 El →
    ctx𝔼 Er →
    Pl⟦El⟦el⟧⟧ = Pr⟦Er⟦er⟧⟧ →
    HeadStepable el →
    HeadStepable er →
    el = er ∧ Pl = Pr ∧ El = Er :=
  by
  intros el er lvl Pl Pr El Er HPl HPr HEl HEr HEq Hel Her
  cases HPl
  case hole =>
    cases HPr
    case hole =>
      simp; apply deterministic.under_ctx𝔼
      apply HEl; apply HEr; apply HEq; apply Hel; apply Her
    case consℚ HQr =>
      exfalso
      apply deterministic.under_ctxℚ_ctx𝔼
      apply HQr; apply HEl; apply HEr
      apply HEq; apply Hel; apply Her
  case consℚ HQl =>
    cases HPr
    case hole =>
      exfalso
      apply deterministic.under_ctxℚ_ctx𝔼
      apply HQl; apply HEr; apply HEl
      symm; apply HEq; apply Her; apply Hel
    case consℚ HQr =>
      have ⟨HEqE, HEqQ⟩ := deterministic.under_ctxℚ _ _ _ _ _ _ _ HQl HQr HEl HEr HEq Hel Her
      have ⟨HEqe, HEqM⟩ := deterministic.under_ctx𝔼 _ _ _ _ HEl HEr HEqE Hel Her
      constructor; apply HEqe
      constructor; apply HEqQ
      apply HEqM

theorem deterministic :
  ∀ σ σl σr e l r,
    (⟨σ, e⟩ ⇝ ⟨σl, l⟩) →
    (⟨σ, e⟩ ⇝ ⟨σr, r⟩) →
    σl = σr ∧ l = r :=
  by
  intros σ σl σr e l r Hstepl Hstepr
  cases Hstepl
  case pure Ml el₀ el₁ HMl Hlcl Hheadl =>
    have Hstepablel := head_pure_impl_head_stepable _ _ Hlcl Hheadl
    generalize HEq : Ml⟦el₀⟧ = e
    rw [HEq] at Hstepr
    cases Hstepr
    case pure Mr er₀ er₁ HMr Hlcr Hheadr =>
      have Hstepabler := head_pure_impl_head_stepable _ _ Hlcr Hheadr
      have ⟨HEqe, HEqM⟩ := deterministic.under_ctx𝕄 _ _ _ _ _ HMl HMr HEq Hstepablel Hstepabler
      rw [HEqe] at Hheadl
      have HEqr := deterministic.head_pure _ _ _ Hheadl Hheadr
      simp [HEqM, HEqr]
    case mutable Mr er₀ er₁ HMr Hlcr Hmutr =>
      exfalso
      have Hstepabler := head_mutable_impl_head_stepable _ _ _ _ Hlcr Hmutr
      have ⟨HEqe, HEqM⟩ := deterministic.under_ctx𝕄 _ _ _ _ _ HMl HMr HEq Hstepablel Hstepabler
      rw [HEqe] at Hheadl
      cases Hmutr <;> nomatch Hheadl
    case reflect Pr Er br HPr HEr Hlcr =>
      exfalso
      have HMr : ctx𝕄 0 (Pr ∘ Er) :=
        by
        apply compose.ctx𝕄_ctx𝔼
        apply rewrite.ctxℙ_ctx𝕄
        apply HPr; apply HEr
      have Hstepabler := reflect_impl_head_stepable _ Hlcr
      have ⟨HEqe, HEqM⟩ := deterministic.under_ctx𝕄 _ _ _ _ _ HMl HMr HEq Hstepablel Hstepabler
      rw [HEqe] at Hheadl
      nomatch Hheadl
  case mutable Ml el₀ el₁ HMl Hlcl Hmutl =>
    have Hstepablel := head_mutable_impl_head_stepable _ _ _ _ Hlcl Hmutl
    generalize HEq : Ml⟦el₀⟧ = e
    rw [HEq] at Hstepr
    cases Hstepr
    case pure Mr er₀ er₁ HMr Hlcr Hheadr =>
      exfalso
      have Hstepabler := head_pure_impl_head_stepable _ _ Hlcr Hheadr
      have ⟨HEqe, HEqM⟩ := deterministic.under_ctx𝕄 _ _ _ _ _ HMl HMr HEq Hstepablel Hstepabler
      rw [HEqe] at Hmutl
      cases Hheadr <;> nomatch Hmutl
    case mutable Mr er₀ er₁ HMr Hlcr Hmutr =>
      have Hstepabler := head_mutable_impl_head_stepable _ _ _ _ Hlcr Hmutr
      have ⟨HEqe, HEqM⟩ := deterministic.under_ctx𝕄 _ _ _ _ _ HMl HMr HEq Hstepablel Hstepabler
      rw [HEqe] at Hmutl
      have ⟨HEqσ, HEqe⟩ := deterministic.head_mutable _ _ _ _ _ _ Hmutl Hmutr
      simp [HEqσ, HEqM, HEqe]
    case reflect Pr Er br HPr HEr Hlcr =>
      exfalso
      have HMr : ctx𝕄 0 (Pr ∘ Er) :=
        by
        apply compose.ctx𝕄_ctx𝔼
        apply rewrite.ctxℙ_ctx𝕄
        apply HPr; apply HEr
      have Hstepabler := reflect_impl_head_stepable _ Hlcr
      have ⟨HEqe, HEqM⟩ := deterministic.under_ctx𝕄 _ _ _ _ _ HMl HMr HEq Hstepablel Hstepabler
      rw [HEqe] at Hmutl
      nomatch Hmutl
  case reflect Pl El bl HPl HEl Hlcl =>
    have HMl : ctx𝕄 0 (Pl ∘ El) :=
      by
      apply compose.ctx𝕄_ctx𝔼
      apply rewrite.ctxℙ_ctx𝕄
      apply HPl; apply HEl
    have Hstepablel := reflect_impl_head_stepable _ Hlcl
    generalize HEq : Pl⟦El⟦.reflect bl⟧⟧ = e
    rw [HEq] at Hstepr
    cases Hstepr
    case pure Mr er₀ er₁ HMr Hlcr Hheadr =>
      exfalso
      have Hstepabler := head_pure_impl_head_stepable _ _ Hlcr Hheadr
      have ⟨HEqe, HEqM⟩ := deterministic.under_ctx𝕄 _ _ _ _ _ HMl HMr HEq Hstepablel Hstepabler
      rw [← HEqe] at Hheadr
      nomatch Hheadr
    case mutable Mr er₀ er₁ HMr Hlcr Hmutr =>
      exfalso
      have Hstepabler := head_mutable_impl_head_stepable _ _ _ _ Hlcr Hmutr
      have ⟨HEqe, HEqM⟩ := deterministic.under_ctx𝕄 _ _ _ _ _ HMl HMr HEq Hstepablel Hstepabler
      rw [← HEqe] at Hmutr
      nomatch Hmutr
    case reflect Pr Er br HPr HEr Hlcr =>
      have Hstepabler := reflect_impl_head_stepable _ Hlcr
      have ⟨HEqr, HEqP, HEqE⟩ := deterministic.under_ctxℙ _ _ _ _ _ _ _ HPl HPr HEl HEr HEq Hstepablel Hstepabler
      simp at HEqr
      simp [HEqr, HEqP, HEqE]
