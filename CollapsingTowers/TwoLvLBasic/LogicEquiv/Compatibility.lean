import CollapsingTowers.TwoLvLBasic.LogicEquiv.LogicRelation

-- Γ ⊧ x ≈ x : Γ(x)
lemma compatibility.fvar :
  ∀ Γ x τ,
    binds x (τ, 𝟙) Γ →
    logic_equiv_typing Γ (.fvar x) (.fvar x) τ :=
  by
  intros Γ x τ Hbinds
  constructor; constructor
  . constructor
  . simp [getr_exists_iff_index_lt_length]
    exists τ, 𝟙
  constructor; constructor
  . constructor
  . simp [getr_exists_iff_index_lt_length]
    exists τ, 𝟙
  intros γ₀ γ₁ HsemΓ
  simp only [logic_equiv_expr]
  exists multi_subst γ₀ (.fvar x), multi_subst γ₁ (.fvar x)
  constructor; apply pure_stepn.refl
  constructor; apply pure_stepn.refl
  apply logic_equiv_env.binds_logic_equiv_value
  apply HsemΓ; apply Hbinds

-- Γ ⊧ n ≈ n : nat
lemma compatibility_lit :
  ∀ Γ n, logic_equiv_typing Γ (.lit n) (.lit n) .nat :=
  by
  intros _ n
  constructor; constructor
  . constructor
  . constructor
  constructor; constructor
  . constructor
  . constructor
  intros γ₀ γ₁ semΓ
  simp only [logic_equiv_expr]
  exists .lit n, .lit n
  simp; apply pure_stepn.refl

-- x ↦ τ𝕒, Γ ⊧ e₀⟦0 ↦ x⟧ ≈ e₁⟦0 ↦ x⟧ : τ𝕓
-- ———————————————————————————————————————
-- Γ ⊧ λ.e₀ ≈ λ.e₁ : τ𝕒 → τ𝕓
theorem compatibility_lam :
  ∀ Γ e₀ e₁ τ𝕒 τ𝕓,
    closed_at (.lam e₀) Γ.length →
    closed_at (.lam e₁) Γ.length →
    logic_equiv_typing ((τ𝕒, .stat) :: Γ) ({0 ↦ Γ.length} e₀) ({0 ↦ Γ.length} e₁) τ𝕓 →
    logic_equiv_typing Γ (.lam e₀) (.lam e₁) (.arrow τ𝕒 τ𝕓 ∅) :=
  by
  intros Γ e₀ e₁ τ𝕒 τ𝕓 Hclosed₀ Hclosed₁ Hsem
  have ⟨Hwf₀, Hwf₁, Hsem⟩ := Hsem
  have Hlc₀ : lc (.lam e₀) := by apply (lc.under_opening _ _ _).mp; apply Hwf₀.left
  have Hlc₁ : lc (.lam e₁) := by apply (lc.under_opening _ _ _).mp; apply Hwf₁.left
  constructor; constructor
  . apply Hlc₀
  . apply Hclosed₀
  constructor; constructor
  . apply Hlc₁
  . apply Hclosed₁
  intros γ₀ γ₁ HsemΓ
  have ⟨Hmulti_wf₀, Hmulti_wf₁⟩ := logic_equiv_env.multi_wf _ _ _ HsemΓ
  have ⟨HEq₀, HEq₁⟩ := logic_equiv_env.length _ _ _ HsemΓ
  simp only [multi_subst.lam, logic_equiv_expr]
  exists .lam (multi_subst γ₀ e₀),.lam (multi_subst γ₁ e₁)
  constructor; apply pure_stepn.refl
  constructor; apply pure_stepn.refl
  simp only [logic_equiv_value]
  constructor; rw [← multi_subst.lam]; constructor
  . apply lc.under_multi_subst; apply Hmulti_wf₀; apply Hlc₀
  . apply closed.under_multi_subst; apply Hmulti_wf₀; rw [HEq₀]; apply Hclosed₀
  constructor; rw [← multi_subst.lam]; constructor
  . apply lc.under_multi_subst; apply Hmulti_wf₁; apply Hlc₁
  . apply closed.under_multi_subst; apply Hmulti_wf₁; rw [HEq₁]; apply Hclosed₁
  intros v₀ v₁ Hsem_value
  have ⟨Hwf₀, Hwf₁⟩ := logic_equiv_value.wf _ _ _ Hsem_value
  rw [← intros.subst γ₀.length (multi_subst γ₀ e₀)]
  rw [← intros.subst γ₁.length (multi_subst γ₁ e₁)]
  rw [← comm.multi_subst_opening, comm.multi_subst_subst, ← multi_subst, HEq₀]
  rw [← comm.multi_subst_opening, comm.multi_subst_subst, ← multi_subst, HEq₁]
  apply Hsem; apply logic_equiv_env.cons; apply Hsem_value; apply HsemΓ
  omega; apply Hwf₁.right; apply Hmulti_wf₁; omega; apply Hmulti_wf₁
  omega; apply Hwf₀.right; apply Hmulti_wf₀; omega; apply Hmulti_wf₀
  . apply closed.inc; apply closed.under_multi_subst
    apply Hmulti_wf₁; rw [HEq₁]; apply Hclosed₁; omega
  . apply closed.inc; apply closed.under_multi_subst
    apply Hmulti_wf₀; rw [HEq₀]; apply Hclosed₀; omega

-- Γ ⊧ f₀ ≈ f₁ : τ𝕒 → τ𝕓
-- Γ ⊧ arg₀ ≈ arg₁ : τ𝕒
-- ——————————————————————————————
-- Γ ⊧ f₀ @ arg₀ ≈ f₁ @ arg₁ : τ𝕓
lemma compatibility_app :
  ∀ Γ f₀ f₁ arg₀ arg₁ τ𝕒 τ𝕓,
    logic_equiv_typing Γ f₀ f₁ (.arrow τ𝕒 τ𝕓 ∅) →
    logic_equiv_typing Γ arg₀ arg₁ τ𝕒 →
    logic_equiv_typing Γ (.app₁ f₀ arg₀) (.app₁ f₁ arg₁) τ𝕓 :=
  by
  intros Γ f₀ f₁ arg₀ arg₁ τ𝕒 τ𝕓 Hf Harg
  have ⟨Hwf_f₀, Hwf_f₁, Hf⟩ := Hf
  have ⟨Hwf_arg₀, Hwf_arg₁, Harg⟩ := Harg
  constructor; constructor
  . constructor; apply Hwf_f₀.left; apply Hwf_arg₀.left
  . constructor; apply Hwf_f₀.right; apply Hwf_arg₀.right
  constructor; constructor
  . constructor; apply Hwf_f₁.left; apply Hwf_arg₁.left
  . constructor; apply Hwf_f₁.right; apply Hwf_arg₁.right
  intros γ₀ γ₁ HsemΓ
  simp only [logic_equiv_expr] at Hf Harg
  have ⟨Hmulti_wf₀, Hmulti_wf₁⟩ := logic_equiv_env.multi_wf _ _ _ HsemΓ
  have ⟨v₀, v₁, Hstepv₀, Hstepv₁, Hsem_value⟩ := Harg γ₀ γ₁ HsemΓ
  have ⟨Hvalue₀, Hvalue₁⟩ := logic_equiv_value.syntactic_value _ _ _ Hsem_value
  have ⟨lam₀, lam₁, Hsteplam₀, Hsteplam₁, Hsem_value_lam⟩ := Hf γ₀ γ₁ HsemΓ
  have ⟨e₀, e₁, HEq₀, HEq₁⟩ := logic_equiv_value.arrow_ty_iff_lam lam₀ lam₁ _ _ Hsem_value_lam
  rw [HEq₀, HEq₁, logic_equiv_value] at Hsem_value_lam
  have ⟨Hwf₀, Hwf₁, Hsem_value_lam⟩ := Hsem_value_lam
  apply logic_equiv_expr.stepn; apply Hsem_value_lam; apply Hsem_value
  . simp
    -- left step
    apply pure_stepn.trans
    apply pure_stepn.congruence_under_ctx𝔹 _ _ _ (ctx𝔹.appl₁ _ _) Hsteplam₀
    apply lc.under_pure_stepn; apply Hstepv₀
    apply lc.value; apply Hvalue₀
    rw [HEq₀]
    -- right step
    apply pure_stepn.trans
    apply pure_stepn.congruence_under_ctx𝔹 _ _ _ (ctx𝔹.appr₁ _ _) Hstepv₀
    apply value.lam; apply Hwf₀.left
    -- head step
    apply pure_stepn.multi _ _ _ _ (pure_stepn.refl _)
    apply pure_step.pure id; apply ctx𝕄.hole
    constructor; apply Hwf₀.left; apply lc.value; apply Hvalue₀
    apply head.app₁; apply Hvalue₀
  . simp
    -- left step
    apply pure_stepn.trans
    apply pure_stepn.congruence_under_ctx𝔹 _ _ _ (ctx𝔹.appl₁ _ _) Hsteplam₁
    apply lc.under_pure_stepn; apply Hstepv₁
    apply lc.value; apply Hvalue₁
    rw [HEq₁]
    -- right step
    apply pure_stepn.trans
    apply pure_stepn.congruence_under_ctx𝔹 _ _ _ (ctx𝔹.appr₁ _ _) Hstepv₁
    apply value.lam; apply Hwf₁.left
    -- head step
    apply pure_stepn.multi _ _ _ _ (pure_stepn.refl _)
    apply pure_step.pure id; apply ctx𝕄.hole
    constructor; apply Hwf₁.left; apply lc.value; apply Hvalue₁
    apply head.app₁; apply Hvalue₁

-- Γ ⊧ b₀ ≈ b₁ : τ𝕒
-- x ↦ τ𝕒, Γ ⊧ e₀⟦0 ↦ x⟧ ≈ e₁⟦0 ↦ x⟧ : τ𝕓
-- ———————————————————————————————————————
-- Γ ⊧ lets b₀ e₀ ≈ lets b₁ e₁ : τ𝕓
lemma compatibility.lets :
  ∀ Γ b₀ b₁ e₀ e₁ τ𝕒 τ𝕓,
    closed_at (.lets b₀ e₀) Γ.length →
    closed_at (.lets b₁ e₁) Γ.length →
    logic_equiv_typing Γ b₀ b₁ τ𝕒 →
    logic_equiv_typing ((τ𝕒, .stat) :: Γ) ({0 ↦ Γ.length} e₀) ({0 ↦ Γ.length} e₁) τ𝕓 →
    logic_equiv_typing Γ (.lets b₀ e₀) (.lets b₁ e₁) τ𝕓 :=
  by
  intros Γ b₀ b₁ e₀ e₁ τ𝕒 τ𝕓 Hclosed₀ Hclosed₁ Hb He
  have ⟨Hwf_b₀, Hwf_b₁, Hb⟩ := Hb
  have ⟨Hwf_e₀, Hwf_e₁, He⟩ := He
  have Hlc₀ : lc (.lets b₀ e₀) :=
    by
    constructor; apply Hwf_b₀.left
    apply (lc.under_opening _ _ _).mp; apply Hwf_e₀.left
  have Hlc₁ : lc (.lets b₁ e₁) :=
    by
    constructor; apply Hwf_b₁.left
    apply (lc.under_opening _ _ _).mp; apply Hwf_e₁.left
  constructor; constructor
  . apply Hlc₀
  . apply Hclosed₀
  constructor; constructor
  . apply Hlc₁
  . apply Hclosed₁
  intros γ₀ γ₁ HsemΓ
  simp only [logic_equiv_expr] at Hb
  have ⟨Hmulti_wf₀, Hmulti_wf₁⟩ := logic_equiv_env.multi_wf _ _ _ HsemΓ
  have ⟨HEq₀, HEq₁⟩ := logic_equiv_env.length _ _ _ HsemΓ
  have ⟨v₀, v₁, Hstepv₀, Hstepv₁, Hsem_value⟩ := Hb γ₀ γ₁ HsemΓ
  have ⟨Hvalue₀, Hvalue₁⟩ := logic_equiv_value.syntactic_value _ _ _ Hsem_value
  have ⟨Hwf₀, Hwf₁⟩ := logic_equiv_value.wf _ _ _ Hsem_value
  apply logic_equiv_expr.stepn; apply He
  apply logic_equiv_env.cons; apply Hsem_value; apply HsemΓ
  . simp
    -- left step
    apply pure_stepn.trans
    apply pure_stepn.congruence_under_ctx𝔹 _ _ _ (ctx𝔹.lets _ _) Hstepv₀
    apply lc.under_multi_subst; apply Hmulti_wf₀; apply Hlc₀.right
    -- head step
    apply pure_stepn.multi _ _ _ _ (pure_stepn.refl _)
    rw [← comm.multi_subst_subst, comm.multi_subst_opening, HEq₀, intros.subst]
    apply pure_step.pure id; apply ctx𝕄.hole
    constructor; apply lc.value; apply Hvalue₀
    apply lc.under_multi_subst; apply Hmulti_wf₀; apply Hlc₀.right
    apply head.lets; apply Hvalue₀
    apply closed.inc; apply closed.under_multi_subst
    apply Hmulti_wf₀; rw [HEq₀]; apply Hclosed₀.right
    omega; omega; apply Hmulti_wf₀
    omega; apply Hwf₀.right; apply Hmulti_wf₀
  . simp
    -- left step
    apply pure_stepn.trans
    apply pure_stepn.congruence_under_ctx𝔹 _ _ _ (ctx𝔹.lets _ _) Hstepv₁
    apply lc.under_multi_subst; apply Hmulti_wf₁; apply Hlc₁.right
    -- head step
    apply pure_stepn.multi _ _ _ _ (pure_stepn.refl _)
    rw [← comm.multi_subst_subst, comm.multi_subst_opening, HEq₁, intros.subst]
    apply pure_step.pure id; apply ctx𝕄.hole
    constructor; apply lc.value; apply Hvalue₁
    apply lc.under_multi_subst; apply Hmulti_wf₁; apply Hlc₁.right
    apply head.lets; apply Hvalue₁
    apply closed.inc; apply closed.under_multi_subst
    apply Hmulti_wf₁; rw [HEq₁]; apply Hclosed₁.right
    omega; omega; apply Hmulti_wf₁
    omega; apply Hwf₁.right; apply Hmulti_wf₁
