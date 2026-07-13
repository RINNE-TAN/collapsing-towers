import Instar.TwoLevelFinal.OperationalSemantics.Confluence
import Instar.TwoLevelFinal.OperationalSemantics.Congruence

-- ⟨σ₀, B⟦e₀⟧⟩ ⭢ ⟨σ₁, r⟩
-- ———————————————————————————————————————————————
-- ⟨σ₀, B⟦e₀⟧⟩ ⭢ ⟨σ₁, B⟦e₁⟧⟩ ∧ ⟨σ₀, e₀⟩ ⭢ ⟨σ₁, e₁⟩
lemma step.refine_at_ctx𝔹 :
  ∀ σ₀ σ₁ B₀ e₀ r,
    ctx𝔹 B₀ →
    ¬value e₀ →
    grounded B₀⟦e₀⟧  →
    (⟨σ₀, B₀⟦e₀⟧⟩ ⭢ ⟨σ₁, r⟩) →
    ∃ e₁, B₀⟦e₁⟧ = r ∧ (⟨σ₀, e₀⟩ ⭢ ⟨σ₁, e₁⟩) :=
  by
  intros σ₀ σ₁ B₀ e₀ r HB₀ HNv HG
  generalize HEqe : B₀⟦e₀⟧ = E₀
  intros Hstep
  cases Hstep
  case pure M e₁ e₂ HM Hlc Hhead =>
    have Hstepable := head_pure_impl_head_stepable _ _ Hlc Hhead
    cases HM
    case hole =>
      exfalso
      apply Hstepable.HAtomic𝔹
      apply HB₀; apply HNv
      symm; apply HEqe
    case cons𝔹 B₁ M HB₁ HM =>
      have HNvM₁ := not_value.under_ctx𝕄 _ _ _ Hstepable.HNv HM
      have ⟨HEqM, HEqB⟩ := deterministic.decomposition_ctx𝔹 _ _ _ _ HB₀ HB₁ HEqe HNv HNvM₁
      exists M⟦e₂⟧
      constructor; simp [HEqB]
      rw [HEqM]; apply step_lvl.pure
      apply HM; apply Hlc; apply Hhead
    case consℝ HR HM =>
      exfalso
      apply deterministic.decomposition_ctx𝔹_ctxℝ
      apply HB₀; apply HR; apply HEqe
      apply HNv; apply not_value.under_ctx𝕄
      apply Hstepable.HNv; apply HM
  case mutable M e₁ e₂ HM Hlc Hmut =>
    have Hstepable := head_mutable_impl_head_stepable _ _ _ _ Hlc Hmut
    cases HM
    case hole =>
      exfalso
      apply Hstepable.HAtomic𝔹
      apply HB₀; apply HNv
      symm; apply HEqe
    case cons𝔹 B₁ M HB₁ HM =>
      have HNvM₁ := not_value.under_ctx𝕄 _ _ _ Hstepable.HNv HM
      have ⟨HEqM, HEqB⟩ := deterministic.decomposition_ctx𝔹 _ _ _ _ HB₀ HB₁ HEqe HNv HNvM₁
      exists M⟦e₂⟧
      constructor; simp [HEqB]
      rw [HEqM]; apply step_lvl.mutable
      apply HM; apply Hlc; apply Hmut
    case consℝ HR HM =>
      exfalso
      apply deterministic.decomposition_ctx𝔹_ctxℝ
      apply HB₀; apply HR; apply HEqe
      apply HNv; apply not_value.under_ctx𝕄
      apply Hstepable.HNv; apply HM
  case reflect M E _ HP HE _ =>
    rw [HEqe] at HG
    have HM := rewrite.ctxℙ_ctx𝕄 _ _ HP
    have HG := grounded.decompose_ctx𝕄 _ _ _ HM HG
    have HG := grounded.decompose_ctx𝔼 _ _ HE HG
    simp at HG

-- ⟨σ₀, B⟦e⟧⟩ ⭢ₖ ⟨σ₁, v⟩
-- ———————————————————————————————————————————————————————————
-- k = i + j ∧ ⟨σ₀, e⟩ ⭢ᵢ ⟨imσ, v𝕖⟩ ∧ ⟨imσ, B⟦v𝕖⟧⟩ ⭢ⱼ ⟨σ₁, v⟩
lemma stepn_indexed.refine_at_ctx𝔹 :
  ∀ σ₀ σ₁ B e₀ v k,
    ctx𝔹 B →
    value v →
    grounded B⟦e₀⟧  →
    (⟨σ₀, B⟦e₀⟧⟩ ⭢ ⟦k⟧ ⟨σ₁, v⟩) →
    ∃ imσ i j v𝕖,
      i + j = k ∧
      value v𝕖 ∧
      (⟨σ₀, e₀⟩ ⭢ ⟦i⟧ ⟨imσ, v𝕖⟩) ∧
      (⟨imσ, B⟦v𝕖⟧⟩ ⭢ ⟦j⟧ ⟨σ₁, v⟩) :=
  by
  intros σ₀ σ₁ B e₀ v k HB
  generalize HEq₀ : (σ₀, B⟦e₀⟧) = st₀
  generalize HEq₁ : (σ₁, v) = st₁
  intros Hvalue HG₀ Hstep
  induction Hstep generalizing e₀ σ₀
  case refl =>
    simp [← HEq₀] at HEq₁
    exfalso; apply not_value.under_ctx𝔹
    apply HB; rw [← HEq₁.right]; apply Hvalue
  case multi k st₀ st₁ st₂ Hstep Hstepn IH =>
    rw [← HEq₀] at Hstep
    match value.decidable e₀ with
    | isTrue Hvalue =>
      exists σ₀, 0, k + 1, e₀
      constructor; omega
      constructor; apply Hvalue
      constructor; apply stepn_indexed.refl
      apply stepn_indexed.multi; apply Hstep; apply Hstepn
    | isFalse HNv =>
      rcases st₁ with ⟨imσ₀, e₁⟩
      have ⟨e₁, HEqe₁, Hstep₀⟩ := step.refine_at_ctx𝔹 _ _ _ _ _ HB HNv HG₀ Hstep
      have HG₁ := grounded.under_step _ _ _ _ Hstep HG₀
      rw [← HEqe₁] at HG₁
      have ⟨imσ₁, i, j, v𝕖, HEqk, Hvalue, Hstep₁, Hstep₂⟩ := IH imσ₀ e₁ (by simp [HEqe₁]) HEq₁ HG₁
      exists imσ₁, i + 1, j, v𝕖
      constructor; omega
      constructor; apply Hvalue
      constructor; apply stepn_indexed.multi
      apply Hstep₀; apply Hstep₁; apply Hstep₂

-- ⟨σ₀, E⟦e⟧⟩ ⭢ₖ ⟨σ₁, v⟩
-- ———————————————————————————————————————————————————————————
-- k = i + j ∧ ⟨σ₀, e⟩ ⭢ᵢ ⟨imσ, v𝕖⟩ ∧ ⟨imσ, E⟦v𝕖⟧⟩ ⭢ⱼ ⟨σ₁, v⟩
lemma stepn_indexed.refine_at_ctx𝔼 :
  ∀ σ₀ σ₁ E e₀ v k,
    ctx𝔼 E →
    value v →
    grounded E⟦e₀⟧  →
    (⟨σ₀, E⟦e₀⟧⟩ ⭢ ⟦k⟧ ⟨σ₁, v⟩) →
    ∃ imσ i j v𝕖,
      i + j = k ∧
      value v𝕖 ∧
      (⟨σ₀, e₀⟩ ⭢ ⟦i⟧ ⟨imσ, v𝕖⟩) ∧
      (⟨imσ, E⟦v𝕖⟧⟩ ⭢ ⟦j⟧ ⟨σ₁, v⟩) :=
  by
  intros σ₀ σ₁ E e₀ v k HE Hvalue HG₀ Hstep
  induction HE generalizing σ₁ v k
  case hole =>
    exists σ₁, k, 0, v
    constructor; rfl
    constructor; apply Hvalue
    constructor; apply Hstep
    apply stepn_indexed.refl
  case cons𝔹 B E HB HE IH =>
    have HGE₀ := grounded.decompose_ctx𝔹 _ _ HB HG₀
    have HGe₀ := grounded.decompose_ctx𝔼 _ _ HE HGE₀
    have ⟨imσ₀, i₀, j₀, v𝕖₀, HEq₀, Hvalue₀, Hstepl₀, Hstepr₀⟩ := stepn_indexed.refine_at_ctx𝔹 _ _ _ _ _ _ HB Hvalue HG₀ Hstep
    have ⟨imσ₁, i₁, j₁, v𝕖₁, HEq₁, Hvalue₁, Hstepl₁, Hstepr₁⟩ := IH _ _ _ Hvalue₀ HGE₀ Hstepl₀
    exists imσ₁, i₁, j₁ + j₀, v𝕖₁
    constructor; omega
    constructor; apply Hvalue₁
    constructor; apply Hstepl₁
    apply stepn_indexed.trans
    apply stepn_indexed_grounded.congruence_under_ctx𝔹 _ _ _ _ _ _ HB
    apply grounded.under_ctx𝔼 _ _ _ HE HGE₀
    apply grounded.under_stepn; apply stepn_indexed_impl_stepn; apply Hstepl₁; apply HGe₀
    apply Hstepr₁; apply Hstepr₀

lemma stepn_indexed.refine.app₁.constructor :
  ∀ σ₀ σ₁ f arg v j,
    value v →
    grounded (.app₁ f arg) →
    (⟨σ₀, .app₁ f arg⟩ ⭢ ⟦j⟧ ⟨σ₁, v⟩) →
    ∃ imσ₀ imσ₁ i₀ i₁ i₂ fᵥ argᵥ,
      i₀ + i₁ + i₂ = j ∧
      value fᵥ ∧ value argᵥ ∧
      (⟨σ₀, f⟩ ⭢ ⟦i₀⟧ ⟨imσ₀, fᵥ⟩) ∧ (⟨imσ₀, arg⟩ ⭢ ⟦i₁⟧ ⟨imσ₁, argᵥ⟩) ∧ ((⟨imσ₁, .app₁ fᵥ argᵥ⟩) ⭢ ⟦i₂⟧ ⟨σ₁, v⟩) :=
  by
  intros σ₀ σ₁ f arg v j Hvalue HG₀ Hstep
  have ⟨HGFun, HGArg⟩ := HG₀
  have Hlc := lc.under_stepn_indexed _ _ _ _ _ Hstep (lc.value _ Hvalue)
  have ⟨imσ₀, i₀, k, fᵥ, HEqj, HvalueFun, Hstep₀, Hstep⟩ := stepn_indexed.refine_at_ctx𝔹 _ _ _ _ _ _ (ctx𝔹.appl₁ _ Hlc.right) Hvalue HG₀ Hstep
  have HGFunᵥ := grounded.under_stepn _ _ _ _ (stepn_indexed_impl_stepn _ _ _ Hstep₀) HGFun
  have HG₁ : grounded (.app₁ fᵥ arg) := by constructor; apply HGFunᵥ; apply HGArg
  have ⟨imσ₁, i₁, i₂, argᵥ, HEqj, HvalueArg, Hstep₁, Hstep₂⟩ := stepn_indexed.refine_at_ctx𝔹 _ _ _ _ _ _ (ctx𝔹.appr₁ _ HvalueFun) Hvalue HG₁ Hstep
  exists imσ₀, imσ₁, i₀, i₁, i₂, fᵥ, argᵥ
  constructor; omega
  constructor; apply HvalueFun
  constructor; apply HvalueArg
  constructor; apply Hstep₀
  constructor; apply Hstep₁
  apply Hstep₂

lemma stepn_indexed.refine.app₁.eliminator :
  ∀ σ₀ σ₁ e arg v j,
    value (.lam e) → value arg → value v →
    (⟨σ₀, .app₁ (.lam e) arg⟩ ⭢ ⟦j⟧ ⟨σ₁, v⟩) →
    ∃ i,
      i + 1 = j ∧
      (⟨σ₀, opening 0 arg e⟩ ⭢ ⟦i⟧ ⟨σ₁, v⟩) :=
  by
  intros σ₀ σ₁ e arg v j HvalueFun HvalueArg Hvalue Hstep
  have HstepHead : ⟨σ₀, .app₁ (.lam e) arg⟩ ⭢ ⟦1⟧ ⟨σ₀, opening 0 arg e⟩ :=
    by
    apply stepn_indexed.multi _ _ _ _ _ (stepn_indexed.refl _)
    apply step_lvl.pure _ _ _ _ ctx𝕄.hole
    constructor; apply lc.value; apply HvalueFun; apply lc.value; apply HvalueArg
    apply head_pure.app₁; apply HvalueArg
  have ⟨z, i, r, HEqIndex, Hstepl, Hstepr⟩ := stepn_indexed.church_rosser _ _ _ _ _ Hstep HstepHead
  have ⟨HEqσ, HEqv, Hz⟩ := stepn_indexed.value_impl_termination _ _ _ _ _ Hvalue Hstepl
  exists i
  constructor; omega
  simp [HEqσ, HEqv]; apply Hstepr

lemma stepn_indexed.refine.binary₁.constructor :
  ∀ σ₀ σ₁ op l r v j,
    value v →
    grounded (.binary₁ op l r) →
    (⟨σ₀, .binary₁ op l r⟩ ⭢ ⟦j⟧ ⟨σ₁, v⟩) →
    ∃ imσ₀ imσ₁ i₀ i₁ i₂ lᵥ rᵥ,
      i₀ + i₁ + i₂ = j ∧
      value lᵥ ∧ value rᵥ ∧
      (⟨σ₀, l⟩ ⭢ ⟦i₀⟧ ⟨imσ₀, lᵥ⟩) ∧ (⟨imσ₀, r⟩ ⭢ ⟦i₁⟧ ⟨imσ₁, rᵥ⟩) ∧ (⟨imσ₁, .binary₁ op lᵥ rᵥ⟩ ⭢ ⟦i₂⟧ ⟨σ₁, v⟩) :=
  by
  intros σ₀ σ₁ op l r v j Hvalue HG₀ Hstep
  have ⟨HGl, HGr⟩ := HG₀
  have Hlc := lc.under_stepn_indexed _ _ _ _ _ Hstep (lc.value _ Hvalue)
  have ⟨imσ₀, i₀, k, lᵥ, HEqj, Hvaluel, Hstep₀, Hstep⟩ := stepn_indexed.refine_at_ctx𝔹 _ _ _ _ _ _ (ctx𝔹.binaryl₁ _ _ Hlc.right) Hvalue HG₀ Hstep
  have HGlᵥ := grounded.under_stepn _ _ _ _ (stepn_indexed_impl_stepn _ _ _ Hstep₀) HGl
  have HG₁ : grounded (.binary₁ op lᵥ r) := by constructor; apply HGlᵥ; apply HGr
  have ⟨imσ₁, i₁, i₂, rᵥ, HEqj, Hvaluer, Hstep₁, Hstep₂⟩ := stepn_indexed.refine_at_ctx𝔹 _ _ _ _ _ _ (ctx𝔹.binaryr₁ _ _ Hvaluel) Hvalue HG₁ Hstep
  exists imσ₀, imσ₁, i₀, i₁, i₂, lᵥ, rᵥ
  constructor; omega
  constructor; apply Hvaluel
  constructor; apply Hvaluer
  constructor; apply Hstep₀
  constructor; apply Hstep₁
  apply Hstep₂

lemma stepn_indexed.refine.binary₁.eliminator :
  ∀ σ₀ σ₁ op l r v j,
    value v →
    (⟨σ₀, .binary₁ op (.lit l) (.lit r)⟩ ⭢ ⟦j⟧ ⟨σ₁, v⟩) →
    σ₀ = σ₁ ∧ 1 = j ∧ v = .lit (eval op l r) :=
  by
  intros σ₀ σ₁ op l r v j Hvalue Hstep
  have HstepHead : ⟨σ₀, .binary₁ op (.lit l) (.lit r)⟩ ⭢ ⟦1⟧ ⟨σ₀, .lit (eval op l r)⟩ :=
    by
    apply stepn_indexed.multi _ _ _ _ _ (stepn_indexed.refl _)
    apply step_lvl.pure _ _ _ _ ctx𝕄.hole
    . simp
    . apply head_pure.binary₁
  have ⟨z₀, z₁, r, HEqIndex, Hstepl, Hstepr⟩ := stepn_indexed.church_rosser _ _ _ _ _ Hstep HstepHead
  have ⟨HEqσ₀, HEqv₀, Hz₀⟩ := stepn_indexed.value_impl_termination _ _ _ _ _ Hvalue Hstepl
  have ⟨HEqσ₁, HEqv₁, Hz₁⟩ := stepn_indexed.value_impl_termination _ _ _ _ _ (value.lit _) Hstepr
  rw [HEqσ₀, HEqv₀, HEqσ₁, HEqv₁]; simp; omega

lemma stepn_indexed.refine.lets :
  ∀ σ₀ σ₁ b e v j,
    value v →
    grounded (.lets b e) →
    (⟨σ₀, .lets b e⟩ ⭢ ⟦j⟧ ⟨σ₁, v⟩) →
    ∃ imσ i₀ i₁ bᵥ,
      i₀ + 1 + i₁ = j ∧
      value bᵥ ∧
      (⟨σ₀, b⟩ ⭢ ⟦i₀⟧ ⟨imσ, bᵥ⟩) ∧ (⟨imσ, opening 0 bᵥ e⟩ ⭢ ⟦i₁⟧ ⟨σ₁, v⟩) :=
  by
  intros σ₀ σ₁ b e v j Hvalue HG Hstep
  have Hlc := lc.under_stepn_indexed _ _ _ _ _ Hstep (lc.value _ Hvalue)
  have ⟨imσ, i₀, k, bᵥ, HEqj, HvalueBind, Hstep₀, Hstep⟩ := stepn_indexed.refine_at_ctx𝔹 _ _ _ _ _ _ (ctx𝔹.lets _ Hlc.right) Hvalue HG Hstep
  have HstepHead : ⟨imσ, .lets bᵥ e⟩ ⭢ ⟦1⟧ ⟨imσ, opening 0 bᵥ e⟩ :=
    by
    apply stepn_indexed.multi _ _ _ _ _ (stepn_indexed.refl _)
    apply step_lvl.pure _ _ _ _ ctx𝕄.hole
    constructor; apply lc.value; apply HvalueBind; apply Hlc.right
    apply head_pure.lets; apply HvalueBind
  have ⟨z, i₁, r, HEqIndex, Hstepl, Hstepr⟩ := stepn_indexed.church_rosser _ _ _ _ _ Hstep HstepHead
  have ⟨HEqσ, HEqv, Hz⟩ := stepn_indexed.value_impl_termination _ _ _ _ _ Hvalue Hstepl
  exists imσ, i₀, i₁, bᵥ
  constructor; omega
  constructor; apply HvalueBind
  constructor; apply Hstep₀
  rw [HEqσ, HEqv]; apply Hstepr

lemma stepn_indexed.refine.fix₁.constructor :
  ∀ σ₀ σ₁ f v j,
    value v →
    grounded (.fix₁ f) →
    (⟨σ₀, .fix₁ f⟩ ⭢ ⟦j⟧ ⟨σ₁, v⟩) →
    ∃ i fᵥ,
      i + 1 = j ∧
      value fᵥ ∧
      (⟨σ₀, f⟩ ⭢ ⟦i⟧ ⟨σ₁, fᵥ⟩) ∧ v = .lam (.app₁ (.app₁ fᵥ (.fix₁ fᵥ)) (.bvar 0)) :=
  by
  intros σ₀ σ₁ f v j Hvalue₀ HG Hstep
  have ⟨imσ, i₀, k, fᵥ, HEqj, HvalueFun, Hstep₀, Hstep⟩ := stepn_indexed.refine_at_ctx𝔹 _ _ _ _ _ _ ctx𝔹.fix₁ Hvalue₀ HG Hstep
  have HstepHead : ⟨imσ, .fix₁ fᵥ⟩ ⭢ ⟦1⟧ ⟨imσ, .lam (.app₁ (.app₁ fᵥ (.fix₁ fᵥ)) (.bvar 0))⟩ :=
    by
    apply stepn_indexed.multi _ _ _ _ _ (stepn_indexed.refl _)
    apply step_lvl.pure _ _ _ _ ctx𝕄.hole
    simp; apply lc.value; apply HvalueFun
    apply head_pure.fix₁; apply HvalueFun
  have Hvalue₁ : value (.lam (.app₁ (.app₁ fᵥ (.fix₁ fᵥ)) (.bvar 0))) :=
    by
    apply value.lam; simp; apply lc.inc
    apply lc.value; apply HvalueFun; omega
  have ⟨z₀, z₁, r, HEqIndex, Hstepl, Hstepr⟩ := stepn_indexed.church_rosser _ _ _ _ _ Hstep HstepHead
  have ⟨HEqσ₀, HEqv₀, Hz₀⟩ := stepn_indexed.value_impl_termination _ _ _ _ _ Hvalue₀ Hstepl
  have ⟨HEqσ₁, HEqv₁, Hz₁⟩ := stepn_indexed.value_impl_termination _ _ _ _ _ Hvalue₁ Hstepr
  exists i₀, fᵥ
  constructor; omega
  constructor; apply HvalueFun
  constructor; rw [HEqσ₀, ← HEqσ₁]; apply Hstep₀
  rw [HEqv₀, HEqv₁]

lemma stepn_indexed.refine.fix₁.eliminator :
  ∀ σ₀ σ₁ f arg v j,
    value f → value arg → value v →
    grounded (.fix₁ f) →
    (⟨σ₀, .app₁ (.lam (.app₁ (.app₁ f (.fix₁ f)) (.bvar 0))) arg⟩ ⭢ ⟦j⟧ ⟨σ₁, v⟩) →
    ∃ i,
      i + 2 = j ∧
      (⟨σ₀, .app₁ (.app₁ f (.lam (.app₁ (.app₁ f (.fix₁ f)) (.bvar 0)))) arg⟩ ⭢ ⟦i⟧ ⟨σ₁, v⟩) :=
  by
  intros σ₀ σ₁ f arg v j HvalueFun HvalueArg Hvalue HG Hstep
  have HstepHead₀ : ⟨σ₀, .app₁ (.lam (.app₁ (.app₁ f (.fix₁ f)) (.bvar 0))) arg⟩ ⭢ ⟨σ₀, .app₁ (.app₁ f (.fix₁ f)) arg⟩ :=
    by
    apply step_lvl.pure _ _ _ _ ctx𝕄.hole
    simp; constructor
    apply lc.inc; apply lc.value; apply HvalueFun; omega
    apply lc.value; apply HvalueArg
    have HEqSubst₀ : .app₁ (.app₁ f (.fix₁ f)) arg = opening 0 arg (.app₁ (.app₁ f (.fix₁ f)) (.bvar 0)) :=
      by
      simp; rw [identity.opening]
      apply lc.inc; apply lc.value; apply HvalueFun; omega
    rw [HEqSubst₀]; apply head_pure.app₁; apply HvalueArg
  have HstepHead₁ : ⟨σ₀, .app₁ (.app₁ f (.fix₁ f)) arg⟩ ⭢ ⟨σ₀, .app₁ (.app₁ f (.lam (.app₁ (.app₁ f (.fix₁ f)) (.bvar 0)))) arg⟩ :=
    by
    apply step_grounded.congruence_under_ctx𝔹 _ _ _ _ _ (ctx𝔹.appl₁ _ (lc.value _ HvalueArg)) (by simp; apply HG)
    apply step_grounded.congruence_under_ctx𝔹 _ _ _ _ _ (ctx𝔹.appr₁ _ HvalueFun) (by simp; apply HG)
    apply step_lvl.pure _ _ _ _ ctx𝕄.hole
    simp; apply lc.value; apply HvalueFun
    apply head_pure.fix₁; apply HvalueFun
  have HstepHead : ⟨σ₀, .app₁ (.lam (.app₁ (.app₁ f (.fix₁ f)) (.bvar 0))) arg⟩ ⭢ ⟦2⟧ ⟨σ₀, .app₁ (.app₁ f (.lam (.app₁ (.app₁ f (.fix₁ f)) (.bvar 0)))) arg⟩ :=
    by
    apply stepn_indexed.multi; apply HstepHead₀
    apply stepn_indexed.multi; apply HstepHead₁
    apply stepn_indexed.refl
  have ⟨z, i, r, HEqIndex, Hstepl, Hstepr⟩ := stepn_indexed.church_rosser _ _ _ _ _ Hstep HstepHead
  have ⟨HEqσ, HEqv, Hz⟩ := stepn_indexed.value_impl_termination _ _ _ _ _ Hvalue Hstepl
  exists i
  constructor; omega
  rw [HEqσ, HEqv]; apply Hstepr

lemma stepn_indexed.refine.alloc₁.constructor :
  ∀ σ₀ σ₁ n v j,
    value v →
    grounded (.alloc₁ n) →
    (⟨σ₀, .alloc₁ n⟩ ⭢ ⟦j⟧ ⟨σ₁, v⟩) →
    ∃ imσ i₀ i₁ nᵥ,
      i₀ + i₁ = j ∧
      value nᵥ ∧
      (⟨σ₀, n⟩ ⭢ ⟦i₀⟧ ⟨imσ, nᵥ⟩) ∧
      (⟨imσ, .alloc₁ nᵥ⟩ ⭢ ⟦i₁⟧ ⟨σ₁, v⟩) :=
  by
  intros σ₀ σ₁ n v j Hvalue HG Hstep
  have ⟨imσ, i₀, i₁, nᵥ, HEqj, HvalueNat, Hstep₀, Hstep⟩ := stepn_indexed.refine_at_ctx𝔹 _ _ _ _ _ _ ctx𝔹.alloc₁ Hvalue HG Hstep
  exists imσ, i₀, i₁, nᵥ

lemma stepn_indexed.refine.alloc₁.eliminator :
  ∀ σ₀ σ₁ n v j,
    value v →
    (⟨σ₀, .alloc₁ (.lit n)⟩ ⭢ ⟦j⟧ ⟨σ₁, v⟩) →
    (.lit n :: σ₀) = σ₁ ∧ 1 = j ∧ v = .loc σ₀.length :=
  by
  intros σ₀ σ₁ n v j Hvalue Hstep
  have HstepHead : ⟨σ₀, .alloc₁ (.lit n)⟩ ⭢ ⟦1⟧ ⟨.lit n :: σ₀, .loc σ₀.length⟩ :=
    by
    apply stepn_indexed.multi _ _ _ _ _ (stepn_indexed.refl _)
    apply step_lvl.mutable _ _ _ _ _ ctx𝕄.hole
    . simp
    . apply head_mutable.alloc₁
  have ⟨z₀, z₁, r, HEqIndex, Hstepl, Hstepr⟩ := stepn_indexed.church_rosser _ _ _ _ _ Hstep HstepHead
  have ⟨HEqσ₀, HEqv₀, Hz₀⟩ := stepn_indexed.value_impl_termination _ _ _ _ _ Hvalue Hstepl
  have ⟨HEqσ₁, HEqv₁, Hz₁⟩ := stepn_indexed.value_impl_termination _ _ _ _ _ (value.loc _) Hstepr
  rw [HEqσ₀, HEqv₀, HEqσ₁, HEqv₁]; simp; omega

lemma stepn_indexed.refine.load₁.constructor :
  ∀ σ₀ σ₁ l v j,
    value v →
    grounded (.load₁ l) →
    (⟨σ₀, .load₁ l⟩ ⭢ ⟦j⟧ ⟨σ₁, v⟩) →
    ∃ imσ i₀ i₁ lᵥ,
      i₀ + i₁ = j ∧
      value lᵥ ∧
      (⟨σ₀, l⟩ ⭢ ⟦i₀⟧ ⟨imσ, lᵥ⟩) ∧
      (⟨imσ, .load₁ lᵥ⟩ ⭢ ⟦i₁⟧ ⟨σ₁, v⟩) :=
  by
  intros σ₀ σ₁ l v j Hvalue HG Hstep
  have ⟨imσ, i₀, i₁, lᵥ, HEqj, HvalueNat, Hstep₀, Hstep⟩ := stepn_indexed.refine_at_ctx𝔹 _ _ _ _ _ _ ctx𝔹.load₁ Hvalue HG Hstep
  exists imσ, i₀, i₁, lᵥ

lemma stepn_indexed.refine.load₁.eliminator :
  ∀ σ₀ σ₁ l v n j,
    value v →
    binds l (Expr.lit n) σ₀ →
    (⟨σ₀, .load₁ (.loc l)⟩ ⭢ ⟦j⟧ ⟨σ₁, v⟩) →
    σ₀ = σ₁ ∧ 1 = j ∧ v = .lit n :=
  by
  intros σ₀ σ₁ l v n j Hvalue Hbinds Hstep
  have HstepHead : ⟨σ₀, .load₁ (.loc l)⟩ ⭢ ⟦1⟧ ⟨σ₀, .lit n⟩ :=
    by
    apply stepn_indexed.multi _ _ _ _ _ (stepn_indexed.refl _)
    apply step_lvl.mutable _ _ _ _ _ ctx𝕄.hole
    . simp
    . apply head_mutable.load₁; apply Hbinds
  have ⟨z₀, z₁, r, HEqIndex, Hstepl, Hstepr⟩ := stepn_indexed.church_rosser _ _ _ _ _ Hstep HstepHead
  have ⟨HEqσ₀, HEqv₀, Hz₀⟩ := stepn_indexed.value_impl_termination _ _ _ _ _ Hvalue Hstepl
  have ⟨HEqσ₁, HEqv₁, Hz₁⟩ := stepn_indexed.value_impl_termination _ _ _ _ _ (value.lit _) Hstepr
  rw [HEqσ₀, HEqv₀, HEqσ₁, HEqv₁]; simp; omega

lemma stepn_indexed.refine.store₁.constructor :
  ∀ σ₀ σ₁ l n v j,
    value v →
    grounded (.store₁ l n) →
    (⟨σ₀, .store₁ l n⟩ ⭢ ⟦j⟧ ⟨σ₁, v⟩) →
    ∃ imσ₀ imσ₁ i₀ i₁ i₂ lᵥ nᵥ,
      i₀ + i₁ + i₂ = j ∧
      value lᵥ ∧
      value nᵥ ∧
      (⟨σ₀, l⟩ ⭢ ⟦i₀⟧ ⟨imσ₀, lᵥ⟩) ∧
      (⟨imσ₀, n⟩ ⭢ ⟦i₁⟧ ⟨imσ₁, nᵥ⟩) ∧
      (⟨imσ₁, .store₁ lᵥ nᵥ⟩ ⭢ ⟦i₂⟧ ⟨σ₁, v⟩) :=
  by
  intros σ₀ σ₁ l n v j Hvalue HG₀ Hstep
  have ⟨HGl, HGn⟩ := HG₀
  have Hlc := lc.under_stepn_indexed _ _ _ _ _ Hstep (lc.value _ Hvalue)
  have ⟨imσ₀, i₀, k, lᵥ, HEqj, Hvaluel, Hstep₀, Hstep⟩ := stepn_indexed.refine_at_ctx𝔹 _ _ _ _ _ _ (ctx𝔹.storel₁ _ Hlc.right) Hvalue HG₀ Hstep
  have HGlᵥ := grounded.under_stepn _ _ _ _ (stepn_indexed_impl_stepn _ _ _ Hstep₀) HGl
  have HG₁ : grounded (.store₁ lᵥ n) := by constructor; apply HGlᵥ; apply HGn
  have ⟨imσ₁, i₁, i₂, nᵥ, HEqj, Hvaluen, Hstep₁, Hstep₂⟩ := stepn_indexed.refine_at_ctx𝔹 _ _ _ _ _ _ (ctx𝔹.storer₁ _ Hvaluel) Hvalue HG₁ Hstep
  exists imσ₀, imσ₁, i₀, i₁, i₂, lᵥ, nᵥ
  constructor; omega
  constructor; apply Hvaluel
  constructor; apply Hvaluen
  constructor; apply Hstep₀
  constructor; apply Hstep₁
  apply Hstep₂

lemma stepn_indexed.refine.store₁.eliminator :
  ∀ σ₀ σ₁ imσ l v n j,
    value v →
    patch l (Expr.lit n) σ₀ imσ →
    (⟨σ₀, .store₁ (.loc l) (.lit n)⟩ ⭢ ⟦j⟧ ⟨σ₁, v⟩) →
    imσ = σ₁ ∧ 1 = j ∧ v = .unit :=
  by
  intros σ₀ σ₁ imσ l v n j Hvalue Hpatch Hstep
  have HstepHead : ⟨σ₀, .store₁ (.loc l) (.lit n)⟩ ⭢ ⟦1⟧ ⟨imσ, .unit⟩ :=
    by
    apply stepn_indexed.multi _ _ _ _ _ (stepn_indexed.refl _)
    apply step_lvl.mutable _ _ _ _ _ ctx𝕄.hole
    . simp
    . apply head_mutable.store₁; apply Hpatch
  have ⟨z₀, z₁, r, HEqIndex, Hstepl, Hstepr⟩ := stepn_indexed.church_rosser _ _ _ _ _ Hstep HstepHead
  have ⟨HEqσ₀, HEqv₀, Hz₀⟩ := stepn_indexed.value_impl_termination _ _ _ _ _ Hvalue Hstepl
  have ⟨HEqσ₁, HEqv₁, Hz₁⟩ := stepn_indexed.value_impl_termination _ _ _ _ _ value.unit Hstepr
  rw [HEqσ₀, HEqv₀, HEqσ₁, HEqv₁]; simp; omega

lemma stepn_indexed.refine.ifz₁.constructor :
  ∀ σ₀ σ₁ c l r v j,
    value v →
    grounded (.ifz₁ c l r) →
    (⟨σ₀, .ifz₁ c l r⟩ ⭢ ⟦j⟧ ⟨σ₁, v⟩) →
    ∃ imσ i₀ i₁ cᵥ,
      i₀ + i₁ = j ∧
      value cᵥ ∧
      (⟨σ₀, c⟩ ⭢ ⟦i₀⟧ ⟨imσ, cᵥ⟩) ∧ (⟨imσ, .ifz₁ cᵥ l r⟩ ⭢ ⟦i₁⟧ ⟨σ₁, v⟩) :=
  by
  intros σ₀ σ₁ c l r v j Hvalue HG₀ Hstep
  have Hlc := lc.under_stepn_indexed _ _ _ _ _ Hstep (lc.value _ Hvalue)
  apply stepn_indexed.refine_at_ctx𝔹 _ _ _ _ _ _ (ctx𝔹.ifz₁ _ _ Hlc.right.left Hlc.right.right) Hvalue HG₀ Hstep

lemma stepn_indexed.refine.ifz₁_then.eliminator :
  ∀ σ₀ σ₁ l r v j,
    value v →
    (⟨σ₀, .ifz₁ (.lit 0) l r⟩ ⭢ ⟦j⟧ ⟨σ₁, v⟩) →
    ∃ i,
      i + 1 = j ∧
      (⟨σ₀, l⟩ ⭢ ⟦i⟧ ⟨σ₁, v⟩) :=
  by
  intros σ₀ σ₁ l r v j Hvalue Hstep
  have Hlc := lc.under_stepn_indexed _ _ _ _ _ Hstep (lc.value _ Hvalue)
  have HstepHead : ⟨σ₀, .ifz₁ (.lit 0) l r⟩ ⭢ ⟦1⟧ ⟨σ₀, l⟩ :=
    by
    apply stepn_indexed.multi _ _ _ _ _ (stepn_indexed.refl _)
    apply step_lvl.pure _ _ _ _ ctx𝕄.hole
    . apply Hlc
    . apply head_pure.ifz₁_then
  have ⟨z, i, r, HEqIndex, Hstepl, Hstepr⟩ := stepn_indexed.church_rosser _ _ _ _ _ Hstep HstepHead
  have ⟨HEqσ, HEqv, Hz⟩ := stepn_indexed.value_impl_termination _ _ _ _ _ Hvalue Hstepl
  exists i
  constructor; omega
  rw [HEqσ, HEqv]; apply Hstepr

lemma stepn_indexed.refine.ifz₁_else.eliminator :
  ∀ σ₀ σ₁ n l r v j,
    value v →
    (⟨σ₀, .ifz₁ (.lit (.succ n)) l r⟩ ⭢ ⟦j⟧ ⟨σ₁, v⟩) →
    ∃ i,
      i + 1 = j ∧
      (⟨σ₀, r⟩ ⭢ ⟦i⟧ ⟨σ₁, v⟩) :=
  by
  intros σ₀ σ₁ n l r v j Hvalue Hstep
  have Hlc := lc.under_stepn_indexed _ _ _ _ _ Hstep (lc.value _ Hvalue)
  have HstepHead : ⟨σ₀, .ifz₁ (.lit (.succ n)) l r⟩ ⭢ ⟦1⟧ ⟨σ₀, r⟩ :=
    by
    apply stepn_indexed.multi _ _ _ _ _ (stepn_indexed.refl _)
    apply step_lvl.pure _ _ _ _ ctx𝕄.hole
    . apply Hlc
    . apply head_pure.ifz₁_else
  have ⟨z, i, r, HEqIndex, Hstepl, Hstepr⟩ := stepn_indexed.church_rosser _ _ _ _ _ Hstep HstepHead
  have ⟨HEqσ, HEqv, Hz⟩ := stepn_indexed.value_impl_termination _ _ _ _ _ Hvalue Hstepl
  exists i
  constructor; omega
  rw [HEqσ, HEqv]; apply Hstepr
