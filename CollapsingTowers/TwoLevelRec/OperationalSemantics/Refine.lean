import CollapsingTowers.TwoLevelRec.OperationalSemantics.Confluence
import CollapsingTowers.TwoLevelRec.OperationalSemantics.Congruence

-- B⟦e₀⟧ ⇝ r
-- ———————————————————————
-- B⟦e₀⟧ ⇝ B⟦e₁⟧ ∧ e₀ ⇝ e₁
lemma step.refine_at_ctx𝔹 :
  ∀ B₀ e₀ r,
    ctx𝔹 B₀ →
    ¬value e₀ →
    grounded B₀⟦e₀⟧  →
    (B₀⟦e₀⟧ ⇝ r) →
    ∃ e₁, B₀⟦e₁⟧ = r ∧ (e₀ ⇝ e₁) :=
  by
  intros B₀ e₀ r HB₀ HNv HG
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
      rw [HEqM]; apply step_lvl.pure
      apply HM; apply Hlc; apply Hhead
    case consℝ HR HM =>
      exfalso
      apply deterministic.under_ctx𝔹_ctxℝ
      apply HB₀; apply HR; apply HEqe
      apply HNv; apply not_value.under_ctx𝕄
      apply Hstepable.HNv; apply HM
  case reflect M E _ HP HE _ =>
    rw [HEqe] at HG
    have HM := rewrite.ctxℙ_ctx𝕄 _ _ HP
    have HG := grounded.decompose_ctx𝕄 _ _ _ HM HG
    have HG := grounded.decompose_ctx𝔼 _ _ HE HG
    simp at HG

-- B⟦e⟧ ⇝ₖ v
-- —————————————————————————————————
-- k = i + j ∧ e ⇝ᵢ v𝕖 ∧ B⟦v𝕖⟧ ⇝ⱼ v
lemma stepn_indexed.refine_at_ctx𝔹 :
  ∀ B e₀ v k,
    ctx𝔹 B →
    value v →
    grounded B⟦e₀⟧  →
    (B⟦e₀⟧ ⇝ ⟦k⟧ v) →
    ∃ i j v𝕖,
      i + j = k ∧
      value v𝕖 ∧
      (e₀ ⇝ ⟦i⟧ v𝕖) ∧
      (B⟦v𝕖⟧ ⇝ ⟦j⟧ v) :=
  by
  intros B e₀ v k HB
  generalize HEqe₀ : B⟦e₀⟧ = E
  intros Hvalue HG₀ Hstep
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
      constructor; apply stepn_indexed.refl
      apply stepn_indexed.multi; apply Hstep; apply Hstepn
    | isFalse HNv =>
      rw [← HEqe₀] at HG₀
      have ⟨e₁, HEqe₁, Hstep₀⟩ := step.refine_at_ctx𝔹 _ _ _ HB HNv HG₀ Hstep
      have HG₁ := grounded.under_step _ _ Hstep HG₀
      have ⟨i, j, v𝕖, HEqk, Hvalue, Hstep₁, Hstep₂⟩ := IH _ HEqe₁ Hvalue HG₁
      exists i + 1, j, v𝕖
      constructor; omega
      constructor; apply Hvalue
      constructor; apply stepn_indexed.multi
      apply Hstep₀; apply Hstep₁; apply Hstep₂

-- E⟦e⟧ ⇝ₖ v
-- —————————————————————————————————
-- k = i + j ∧ e ⇝ᵢ v𝕖 ∧ E⟦v𝕖⟧ ⇝ⱼ v
lemma stepn_indexed.refine_at_ctx𝔼 :
  ∀ E e₀ v k,
    ctx𝔼 E →
    value v →
    grounded E⟦e₀⟧  →
    (E⟦e₀⟧ ⇝ ⟦k⟧ v) →
    ∃ i j v𝕖,
      i + j = k ∧
      value v𝕖 ∧
      (e₀ ⇝ ⟦i⟧ v𝕖) ∧
      (E⟦v𝕖⟧ ⇝ ⟦j⟧ v) :=
  by
  intros E e₀ v k HE Hvalue HG₀ Hstep
  induction HE generalizing v k
  case hole =>
    exists k, 0, v
    constructor; rfl
    constructor; apply Hvalue
    constructor; apply Hstep
    apply stepn_indexed.refl
  case cons𝔹 B E HB HE IH =>
    have HGE₀ := grounded.decompose_ctx𝔹 _ _ HB HG₀
    have HGe₀ := grounded.decompose_ctx𝔼 _ _ HE HGE₀
    have ⟨i₀, j₀, v𝕖₀, HEq₀, Hvalue₀, Hstepl₀, Hstepr₀⟩ := stepn_indexed.refine_at_ctx𝔹 _ _ _ _ HB Hvalue HG₀ Hstep
    have ⟨i₁, j₁, v𝕖₁, HEq₁, Hvalue₁, Hstepl₁, Hstepr₁⟩ := IH _ _ Hvalue₀ HGE₀ Hstepl₀
    exists i₁, j₁ + j₀, v𝕖₁
    constructor; omega
    constructor; apply Hvalue₁
    constructor; apply Hstepl₁
    apply stepn_indexed.trans
    apply stepn_indexed_grounded.congruence_under_ctx𝔹 _ _ _ _ HB
    apply grounded.under_ctx𝔼 _ _ _ HE HGE₀
    apply grounded.under_stepn; apply stepn_indexed_impl_stepn; apply Hstepl₁; apply HGe₀
    apply Hstepr₁; apply Hstepr₀

lemma stepn_indexed.refine.app₁.constructor :
  ∀ f arg v j,
    value v →
    grounded (.app₁ f arg) →
    ((.app₁ f arg) ⇝ ⟦j⟧ v) →
    ∃ i₀ i₁ i₂ fᵥ argᵥ,
      i₀ + i₁ + i₂ = j ∧
      value fᵥ ∧ value argᵥ ∧
      (f ⇝ ⟦i₀⟧ fᵥ) ∧ (arg ⇝ ⟦i₁⟧ argᵥ) ∧ ((.app₁ fᵥ argᵥ) ⇝ ⟦i₂⟧ v) :=
  by
  intros f arg v j Hvalue HG₀ Hstep
  have ⟨HGFun, HGArg⟩ := HG₀
  have Hlc := lc.under_stepn_indexed _ _ _ Hstep (lc.value _ Hvalue)
  have ⟨i₀, k, fᵥ, HEqj, HvalueFun, Hstep₀, Hstep⟩ := stepn_indexed.refine_at_ctx𝔹 _ _ _ _ (ctx𝔹.appl₁ _ Hlc.right) Hvalue HG₀ Hstep
  have HGFunᵥ := grounded.under_stepn _ _ (stepn_indexed_impl_stepn _ _ _ Hstep₀) HGFun
  have HG₁ : grounded (.app₁ fᵥ arg) := by constructor; apply HGFunᵥ; apply HGArg
  have ⟨i₁, i₂, argᵥ, HEqj, HvalueArg, Hstep₁, Hstep₂⟩ := stepn_indexed.refine_at_ctx𝔹 _ _ _ _ (ctx𝔹.appr₁ _ HvalueFun) Hvalue HG₁ Hstep
  exists i₀, i₁, i₂, fᵥ, argᵥ
  constructor; omega
  constructor; apply HvalueFun
  constructor; apply HvalueArg
  constructor; apply Hstep₀
  constructor; apply Hstep₁
  apply Hstep₂

lemma stepn_indexed.refine.app₁.eliminator :
  ∀ e arg v j,
    value (.lam e) → value arg → value v →
    ((.app₁ (.lam e) arg) ⇝ ⟦j⟧ v) →
    ∃ i,
      i + 1 = j ∧
      ((opening 0 arg e) ⇝ ⟦i⟧ v) :=
  by
  intros e arg v j HvalueFun HvalueArg Hvalue Hstep
  have HstepHead : (.app₁ (.lam e) arg) ⇝ ⟦1⟧ (opening 0 arg e) :=
    by
    apply stepn_indexed.multi _ _ _ _ _ (stepn_indexed.refl _)
    apply step_lvl.pure _ _ _ ctx𝕄.hole
    constructor; apply lc.value; apply HvalueFun; apply lc.value; apply HvalueArg
    apply head.app₁; apply HvalueArg
  have ⟨z, i, r, HEqIndex, Hstepl, Hstepr⟩ := stepn_indexed.church_rosser _ _ _ _ _ Hstep HstepHead
  have ⟨HEqv, Hz⟩ := stepn_indexed.value_impl_termination _ _ _ Hvalue Hstepl
  exists i
  constructor; omega
  rw [HEqv]; apply Hstepr

lemma stepn_indexed.refine.binary₁.constructor :
  ∀ op l r v j,
    value v →
    grounded (.binary₁ op l r) →
    ((.binary₁ op l r) ⇝ ⟦j⟧ v) →
    ∃ i₀ i₁ i₂ lᵥ rᵥ,
      i₀ + i₁ + i₂ = j ∧
      value lᵥ ∧ value rᵥ ∧
      (l ⇝ ⟦i₀⟧ lᵥ) ∧ (r ⇝ ⟦i₁⟧ rᵥ) ∧ ((.binary₁ op lᵥ rᵥ) ⇝ ⟦i₂⟧ v) :=
  by
  intros op l r v j Hvalue HG₀ Hstep
  have ⟨HGl, HGr⟩ := HG₀
  have Hlc := lc.under_stepn_indexed _ _ _ Hstep (lc.value _ Hvalue)
  have ⟨i₀, k, lᵥ, HEqj, Hvaluel, Hstep₀, Hstep⟩ := stepn_indexed.refine_at_ctx𝔹 _ _ _ _ (ctx𝔹.binaryl₁ _ _ Hlc.right) Hvalue HG₀ Hstep
  have HGlᵥ := grounded.under_stepn _ _ (stepn_indexed_impl_stepn _ _ _ Hstep₀) HGl
  have HG₁ : grounded (.binary₁ op lᵥ r) := by constructor; apply HGlᵥ; apply HGr
  have ⟨i₁, i₂, rᵥ, HEqj, Hvaluer, Hstep₁, Hstep₂⟩ := stepn_indexed.refine_at_ctx𝔹 _ _ _ _ (ctx𝔹.binaryr₁ _ _ Hvaluel) Hvalue HG₁ Hstep
  exists i₀, i₁, i₂, lᵥ, rᵥ
  constructor; omega
  constructor; apply Hvaluel
  constructor; apply Hvaluer
  constructor; apply Hstep₀
  constructor; apply Hstep₁
  apply Hstep₂

lemma stepn_indexed.refine.binary₁.eliminator :
  ∀ op l r v j,
    value v →
    ((.binary₁ op (.lit l) (.lit r)) ⇝ ⟦j⟧ v) →
    1 = j ∧ v = .lit (eval op l r) :=
  by
  intros op l r v j Hvalue Hstep
  have HstepHead : (.binary₁ op (.lit l) (.lit r)) ⇝ ⟦1⟧ .lit (eval op l r) :=
    by
    apply stepn_indexed.multi _ _ _ _ _ (stepn_indexed.refl _)
    apply step_lvl.pure _ _ _ ctx𝕄.hole
    . simp
    . apply head.binary₁
  have ⟨z₀, z₁, r, HEqIndex, Hstepl, Hstepr⟩ := stepn_indexed.church_rosser _ _ _ _ _ Hstep HstepHead
  have ⟨HEqv₀, Hz₀⟩ := stepn_indexed.value_impl_termination _ _ _ Hvalue Hstepl
  have ⟨HEqv₁, Hz₁⟩ := stepn_indexed.value_impl_termination _ _ _ (value.lit _) Hstepr
  rw [HEqv₀, HEqv₁]; simp; omega

lemma stepn_indexed.refine.lets :
  ∀ b e v j,
    value v →
    grounded (.lets b e) →
    ((.lets b e) ⇝ ⟦j⟧ v) →
    ∃ i₀ i₁ bᵥ,
      i₀ + 1 + i₁ = j ∧
      value bᵥ ∧
      (b ⇝ ⟦i₀⟧ bᵥ) ∧ ((opening 0 bᵥ e) ⇝ ⟦i₁⟧ v) :=
  by
  intros b e v j Hvalue HG Hstep
  have Hlc := lc.under_stepn_indexed _ _ _ Hstep (lc.value _ Hvalue)
  have ⟨i₀, k, bᵥ, HEqj, HvalueBind, Hstep₀, Hstep⟩ := stepn_indexed.refine_at_ctx𝔹 _ _ _ _ (ctx𝔹.lets _ Hlc.right) Hvalue HG Hstep
  have HstepHead : (.lets bᵥ e) ⇝ ⟦1⟧ (opening 0 bᵥ e) :=
    by
    apply stepn_indexed.multi _ _ _ _ _ (stepn_indexed.refl _)
    apply step_lvl.pure _ _ _ ctx𝕄.hole
    constructor; apply lc.value; apply HvalueBind; apply Hlc.right
    apply head.lets; apply HvalueBind
  have ⟨z, i₁, r, HEqIndex, Hstepl, Hstepr⟩ := stepn_indexed.church_rosser _ _ _ _ _ Hstep HstepHead
  have ⟨HEqv, Hz⟩ := stepn_indexed.value_impl_termination _ _ _ Hvalue Hstepl
  exists i₀, i₁, bᵥ
  constructor; omega
  constructor; apply HvalueBind
  constructor; apply Hstep₀
  rw [HEqv]; apply Hstepr

lemma stepn_indexed.refine.fix₁.constructor :
  ∀ f v j,
    value v →
    grounded (.fix₁ f) →
    ((.fix₁ f) ⇝ ⟦j⟧ v) →
    ∃ i fᵥ,
      i + 1 = j ∧
      value fᵥ ∧
      (f ⇝ ⟦i⟧ fᵥ) ∧ v = .lam (.app₁ (.app₁ fᵥ (.fix₁ fᵥ)) (.bvar 0)) :=
  by
  intros f v j Hvalue₀ HG Hstep
  have ⟨i₀, k, fᵥ, HEqj, HvalueFun, Hstep₀, Hstep⟩ := stepn_indexed.refine_at_ctx𝔹 _ _ _ _ ctx𝔹.fix₁ Hvalue₀ HG Hstep
  have HstepHead : (.fix₁ fᵥ) ⇝ ⟦1⟧ .lam (.app₁ (.app₁ fᵥ (.fix₁ fᵥ)) (.bvar 0)) :=
    by
    apply stepn_indexed.multi _ _ _ _ _ (stepn_indexed.refl _)
    apply step_lvl.pure _ _ _ ctx𝕄.hole
    simp; apply lc.value; apply HvalueFun
    apply head.fix₁; apply HvalueFun
  have Hvalue₁ : value (.lam (.app₁ (.app₁ fᵥ (.fix₁ fᵥ)) (.bvar 0))) :=
    by
    apply value.lam; simp; apply lc.inc
    apply lc.value; apply HvalueFun; omega
  have ⟨z₀, z₁, r, HEqIndex, Hstepl, Hstepr⟩ := stepn_indexed.church_rosser _ _ _ _ _ Hstep HstepHead
  have ⟨HEqv₀, Hz₀⟩ := stepn_indexed.value_impl_termination _ _ _ Hvalue₀ Hstepl
  have ⟨HEqv₁, Hz₁⟩ := stepn_indexed.value_impl_termination _ _ _ Hvalue₁ Hstepr
  exists i₀, fᵥ
  constructor; omega
  constructor; apply HvalueFun
  constructor; apply Hstep₀
  rw [HEqv₀, HEqv₁]

lemma stepn_indexed.refine.fix₁.eliminator :
  ∀ f arg v j,
    value f → value arg → value v →
    grounded (.fix₁ f) →
    ((.app₁ (.lam (.app₁ (.app₁ f (.fix₁ f)) (.bvar 0))) arg) ⇝ ⟦j⟧ v) →
    ∃ i,
      i + 2 = j ∧
      (.app₁ (.app₁ f (.lam (.app₁ (.app₁ f (.fix₁ f)) (.bvar 0)))) arg) ⇝ ⟦i⟧ v :=
  by
  intros f arg v j HvalueFun HvalueArg Hvalue HG Hstep
  have HstepHead₀ : (.app₁ (.lam (.app₁ (.app₁ f (.fix₁ f)) (.bvar 0))) arg) ⇝ (.app₁ (.app₁ f (.fix₁ f)) arg) :=
    by
    apply step_lvl.pure _ _ _ ctx𝕄.hole
    simp; constructor
    apply lc.inc; apply lc.value; apply HvalueFun; omega
    apply lc.value; apply HvalueArg
    have HEqSubst₀ : .app₁ (.app₁ f (.fix₁ f)) arg = opening 0 arg (.app₁ (.app₁ f (.fix₁ f)) (.bvar 0)) :=
      by
      simp; rw [identity.opening]
      apply lc.inc; apply lc.value; apply HvalueFun; omega
    rw [HEqSubst₀]; apply head.app₁; apply HvalueArg
  have HstepHead₁ : (.app₁ (.app₁ f (.fix₁ f)) arg) ⇝ (.app₁ (.app₁ f (.lam (.app₁ (.app₁ f (.fix₁ f)) (.bvar 0)))) arg) :=
    by
    apply step_grounded.congruence_under_ctx𝔹 _ _ _ (ctx𝔹.appl₁ _ (lc.value _ HvalueArg)) (by simp; apply HG)
    apply step_grounded.congruence_under_ctx𝔹 _ _ _ (ctx𝔹.appr₁ _ HvalueFun) (by simp; apply HG)
    apply step_lvl.pure _ _ _ ctx𝕄.hole
    simp; apply lc.value; apply HvalueFun
    apply head.fix₁; apply HvalueFun
  have HstepHead : (.app₁ (.lam (.app₁ (.app₁ f (.fix₁ f)) (.bvar 0))) arg) ⇝ ⟦2⟧ (.app₁ (.app₁ f (.lam (.app₁ (.app₁ f (.fix₁ f)) (.bvar 0)))) arg) :=
    by
    apply stepn_indexed.multi; apply HstepHead₀
    apply stepn_indexed.multi; apply HstepHead₁
    apply stepn_indexed.refl
  have ⟨z, i, r, HEqIndex, Hstepl, Hstepr⟩ := stepn_indexed.church_rosser _ _ _ _ _ Hstep HstepHead
  have ⟨HEqv, Hz⟩ := stepn_indexed.value_impl_termination _ _ _ Hvalue Hstepl
  exists i
  constructor; omega
  rw [HEqv]; apply Hstepr

lemma stepn_indexed.refine.ifz₁.constructor :
  ∀ c l r v j,
    value v →
    grounded (.ifz₁ c l r) →
    ((.ifz₁ c l r) ⇝ ⟦j⟧ v) →
    ∃ i₀ i₁ cᵥ,
      i₀ + i₁ = j ∧
      value cᵥ ∧
      (c ⇝ ⟦i₀⟧ cᵥ) ∧ ((.ifz₁ cᵥ l r) ⇝ ⟦i₁⟧ v) :=
  by
  intros op l r v j Hvalue HG₀ Hstep
  have Hlc := lc.under_stepn_indexed _ _ _ Hstep (lc.value _ Hvalue)
  apply stepn_indexed.refine_at_ctx𝔹 _ _ _ _ (ctx𝔹.ifz₁ _ _ Hlc.right.left Hlc.right.right) Hvalue HG₀ Hstep

lemma stepn_indexed.refine.ifz₁_then.eliminator :
  ∀ l r v j,
    value v →
    ((.ifz₁ (.lit 0) l r) ⇝ ⟦j⟧ v) →
    ∃ i,
      i + 1 = j ∧
      (l ⇝ ⟦i⟧ v) :=
  by
  intros l r v j Hvalue Hstep
  have Hlc := lc.under_stepn_indexed _ _ _ Hstep (lc.value _ Hvalue)
  have HstepHead : (.ifz₁ (.lit 0) l r) ⇝ ⟦1⟧ l :=
    by
    apply stepn_indexed.multi _ _ _ _ _ (stepn_indexed.refl _)
    apply step_lvl.pure _ _ _ ctx𝕄.hole
    . apply Hlc
    . apply head.ifz₁_then
  have ⟨z, i, r, HEqIndex, Hstepl, Hstepr⟩ := stepn_indexed.church_rosser _ _ _ _ _ Hstep HstepHead
  have ⟨HEqv, Hz⟩ := stepn_indexed.value_impl_termination _ _ _ Hvalue Hstepl
  exists i
  constructor; omega
  rw [HEqv]; apply Hstepr

lemma stepn_indexed.refine.ifz₁_else.eliminator :
  ∀ n l r v j,
    value v →
    ((.ifz₁ (.lit (.succ n)) l r) ⇝ ⟦j⟧ v) →
    ∃ i,
      i + 1 = j ∧
      (r ⇝ ⟦i⟧ v) :=
  by
  intros n l r v j Hvalue Hstep
  have Hlc := lc.under_stepn_indexed _ _ _ Hstep (lc.value _ Hvalue)
  have HstepHead : (.ifz₁ (.lit (.succ n)) l r) ⇝ ⟦1⟧ r :=
    by
    apply stepn_indexed.multi _ _ _ _ _ (stepn_indexed.refl _)
    apply step_lvl.pure _ _ _ ctx𝕄.hole
    . apply Hlc
    . apply head.ifz₁_else
  have ⟨z, i, r, HEqIndex, Hstepl, Hstepr⟩ := stepn_indexed.church_rosser _ _ _ _ _ Hstep HstepHead
  have ⟨HEqv, Hz⟩ := stepn_indexed.value_impl_termination _ _ _ Hvalue Hstepl
  exists i
  constructor; omega
  rw [HEqv]; apply Hstepr
