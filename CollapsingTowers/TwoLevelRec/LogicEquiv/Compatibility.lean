import CollapsingTowers.TwoLevelRec.LogicEquiv.LogicRelation

-- Γ ⊧ x ≤𝑙𝑜𝑔 x : Γ(x)
lemma compatibility.fvar :
  ∀ Γ x τ,
    binds x (τ, 𝟙) Γ →
    logic_rel_typing Γ (.fvar x) (.fvar x) τ :=
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
  intros k γ₀ γ₁ HsemΓ
  simp only [logic_rel_expr]
  intros j Hindex v₀ Hvalue₀ Hstep₀
  exists multi_subst γ₁ (.fvar x)
  constructor
  . apply pure_stepn.refl
  . have Hsem_value := logic_rel_env.binds_logic_rel_value _ _ _ _ _ _ HsemΓ Hbinds
    have ⟨Hvalue₀, Hvalue₁⟩ := logic_rel_value.syntactic_value _ _ _ _ Hsem_value
    have ⟨HEqv, Hj⟩ := pure_stepn_indexed.value_impl_termination _ _ _ Hvalue₀ Hstep₀
    rw [← HEqv, Hj]; apply Hsem_value

-- Γ ⊧ n ≤𝑙𝑜𝑔 n : ℕ
lemma compatibility.lit :
  ∀ Γ n, logic_rel_typing Γ (.lit n) (.lit n) .nat :=
  by
  intros _ n
  constructor; constructor
  . constructor
  . constructor
  constructor; constructor
  . constructor
  . constructor
  intros k γ₀ γ₁ semΓ
  simp only [logic_rel_expr]
  intros j Hindex v₀ Hvalue₀ Hstep₀
  exists .lit n
  constructor
  . simp; apply pure_stepn.refl
  . simp at Hstep₀
    have ⟨HEqv, Hj⟩ := pure_stepn_indexed.value_impl_termination _ _ _ (value.lit n) Hstep₀
    simp [← HEqv, Hj]

-- x ↦ τ𝕒, Γ ⊧ e₀⟦0 ↦ x⟧ ≤𝑙𝑜𝑔 e₁⟦0 ↦ x⟧ : τ𝕓
-- ———————————————————————————————————————
-- Γ ⊧ λ.e₀ ≤𝑙𝑜𝑔 λ.e₁ : τ𝕒 → τ𝕓
lemma compatibility.lam :
  ∀ Γ e₀ e₁ τ𝕒 τ𝕓,
    closed_at (.lam e₀) Γ.length →
    closed_at (.lam e₁) Γ.length →
    logic_rel_typing ((τ𝕒, 𝟙) :: Γ) ({0 ↦ Γ.length} e₀) ({0 ↦ Γ.length} e₁) τ𝕓 →
    logic_rel_typing Γ (.lam e₀) (.lam e₁) (.arrow τ𝕒 τ𝕓 ∅) :=
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
  intros k γ₀ γ₁ HsemΓ
  have ⟨Hmulti_wf₀, Hmulti_wf₁⟩ := logic_rel_env.multi_wf _ _ _ _ HsemΓ
  have ⟨HEq₀, HEq₁⟩ := logic_rel_env.length _ _ _ _ HsemΓ
  rw [logic_rel_expr]
  intros j Hindexj lam₀ HvalueLam₀ Hstep₀
  exists multi_subst γ₁ (.lam e₁)
  constructor; apply pure_stepn.refl
  have Hvalue_lam₀ : value (multi_subst γ₀ (.lam e₀)) :=
    by
    simp; apply value.lam; rw [← multi_subst.lam]
    apply lc.under_multi_subst
    apply Hmulti_wf₀; apply Hlc₀
  have ⟨HEq_lam₀, Hj⟩ := pure_stepn_indexed.value_impl_termination _ _ _ Hvalue_lam₀ Hstep₀
  simp only [← HEq_lam₀, Hj, multi_subst.lam, logic_rel_value]
  constructor; constructor
  . rw [← multi_subst.lam]
    apply lc.under_multi_subst
    apply Hmulti_wf₀; apply Hlc₀
  . rw [← multi_subst.lam]
    apply closed.under_multi_subst
    apply Hmulti_wf₀; rw [HEq₀]; apply Hclosed₀
  constructor; constructor
  . rw [← multi_subst.lam]
    apply lc.under_multi_subst
    apply Hmulti_wf₁; apply Hlc₁
  . rw [← multi_subst.lam]
    apply closed.under_multi_subst
    apply Hmulti_wf₁; rw [HEq₁]; apply Hclosed₁
  intros j Hindexj argv₀ argv₁ Hsem_value_arg
  have ⟨HvalueArg₀, HvalueArg₁⟩ := logic_rel_value.syntactic_value _ _ _ _ Hsem_value_arg
  have ⟨HwfArg₀, HwfArg₁⟩ := logic_rel_value.wf _ _ _ _ Hsem_value_arg
  apply logic_rel_expr.stepn j 1; apply Hsem _ (argv₀ :: γ₀) (argv₁ :: γ₁)
  apply logic_rel_env.cons; apply logic_rel_value.weakening; apply Hsem_value_arg; omega
  apply logic_rel_env.weakening; apply HsemΓ; omega
  . apply pure_stepn_indexed.multi _ _ _ _ _ (pure_stepn_indexed.refl _)
    rw [multi_subst, ← comm.multi_subst_subst, comm.multi_subst_opening]
    rw [HEq₀, intros.subst]
    apply pure_step.pure id; apply ctx𝕄.hole
    constructor
    . rw [← multi_subst.lam]
      apply lc.under_multi_subst
      apply Hmulti_wf₀; apply Hlc₀
    . apply lc.value; apply HvalueArg₀
    apply head.app₁; apply HvalueArg₀
    apply closed.inc; apply closed.under_multi_subst; apply Hmulti_wf₀
    rw [HEq₀]; apply Hclosed₀; omega
    omega; apply Hmulti_wf₀; omega
    apply HwfArg₀.right; apply Hmulti_wf₀
  . apply pure_stepn.multi _ _ _ _ (pure_stepn.refl _)
    rw [multi_subst, ← comm.multi_subst_subst, comm.multi_subst_opening]
    rw [HEq₁, intros.subst]
    apply pure_step.pure id; apply ctx𝕄.hole
    constructor
    . rw [← multi_subst.lam]
      apply lc.under_multi_subst
      apply Hmulti_wf₁; apply Hlc₁
    . apply lc.value; apply HvalueArg₁
    apply head.app₁; apply HvalueArg₁
    apply closed.inc; apply closed.under_multi_subst; apply Hmulti_wf₁
    rw [HEq₁]; apply Hclosed₁; omega
    omega; apply Hmulti_wf₁; omega
    apply HwfArg₁.right; apply Hmulti_wf₁

-- Γ ⊧ f₀ ≤𝑙𝑜𝑔 f₁ : τ𝕒 → τ𝕓
-- Γ ⊧ arg₀ ≤𝑙𝑜𝑔 arg₁ : τ𝕒
-- —————————————————————————————————
-- Γ ⊧ f₀ @ arg₀ ≤𝑙𝑜𝑔 f₁ @ arg₁ : τ𝕓
lemma compatibility.app :
  ∀ Γ f₀ f₁ arg₀ arg₁ τ𝕒 τ𝕓,
    logic_rel_typing Γ f₀ f₁ (.arrow τ𝕒 τ𝕓 ∅) →
    logic_rel_typing Γ arg₀ arg₁ τ𝕒 →
    logic_rel_typing Γ (.app₁ f₀ arg₀) (.app₁ f₁ arg₁) τ𝕓 :=
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
  intros k γ₀ γ₁ HsemΓ
  have ⟨Hmulti_wf₀, Hmulti_wf₁⟩ := logic_rel_env.multi_wf _ _ _ _ HsemΓ
  rw [logic_rel_expr]
  intros j Hindex v₀ Hvalue₀ Hstep₀
  simp at Hstep₀
  have ⟨i₀, i₁, i₂, fv₀, argv₀, HEqj, HvalueF₀, HvalueArg₀, HstepF₀, HstepArg₀, HstepHead₀⟩ := pure_stepn_indexed.refine.app₁ _ _ _ _ Hvalue₀ Hstep₀
  simp only [logic_rel_expr] at Hf Harg
  have ⟨fv₁, HstepF₁, Hsem_value_f⟩ := Hf _ _ _ HsemΓ i₀ (by omega) _ HvalueF₀ HstepF₀
  have ⟨argv₁, HstepArg₁, Hsem_value_arg⟩ := Harg _ _ _ HsemΓ i₁ (by omega) _ HvalueArg₀ HstepArg₀
  have Hsem_value_f : logic_rel_value (k - i₀ - i₁) fv₀ fv₁ (τ𝕒.arrow τ𝕓 ∅) := logic_rel_value.weakening _ _ _ _ _ Hsem_value_f (by omega)
  have Hsem_value_arg : logic_rel_value (k - i₀ - i₁) argv₀ argv₁ τ𝕒 := logic_rel_value.weakening _ _ _ _ _ Hsem_value_arg (by omega)
  have ⟨e₀, e₁, HEq₀, HEq₁⟩ := logic_rel_value.arrow_ty_iff_lam _ fv₀ fv₁ _ _ Hsem_value_f
  rw [HEq₀] at HstepF₀ HstepHead₀ Hsem_value_f
  rw [HEq₁] at HstepF₁ Hsem_value_f
  simp only [logic_rel_value] at Hsem_value_f
  have ⟨Hwf₀, Hwf₁, Hsem_value_f⟩ := Hsem_value_f
  have Hsem_expr := Hsem_value_f (k - i₀ - i₁) (by omega) _ _ Hsem_value_arg
  simp only [logic_rel_expr] at Hsem_expr
  have ⟨v₁, HstepHead₁, Hsem_value⟩ := Hsem_expr i₂ (by omega) v₀ Hvalue₀ HstepHead₀
  exists v₁; constructor
  . simp
    apply pure_stepn.trans
    -- left step
    apply pure_stepn.congruence_under_ctx𝔹 _ _ _ (ctx𝔹.appl₁ _ _) HstepF₁
    apply lc.under_multi_subst; apply Hmulti_wf₁; apply Hwf_arg₁.left
    -- right step
    apply pure_stepn.trans
    apply pure_stepn.congruence_under_ctx𝔹 _ _ _ (ctx𝔹.appr₁ _ _) HstepArg₁
    apply value.lam; apply Hwf₁.left
    -- head step
    apply HstepHead₁
  . have HEq : k - j = k - i₀ - i₁ - i₂ := by omega
    rw [HEq]; apply Hsem_value

-- Γ ⊧ b₀ ≤𝑙𝑜𝑔 b₁ : τ𝕒
-- x ↦ τ𝕒, Γ ⊧ e₀⟦0 ↦ x⟧ ≤𝑙𝑜𝑔 e₁⟦0 ↦ x⟧ : τ𝕓
-- ———————————————————————————————————————
-- Γ ⊧ lets b₀ e₀ ≤𝑙𝑜𝑔 lets b₁ e₁ : τ𝕓
lemma compatibility.lets :
  ∀ Γ b₀ b₁ e₀ e₁ τ𝕒 τ𝕓,
    closed_at (.lets b₀ e₀) Γ.length →
    closed_at (.lets b₁ e₁) Γ.length →
    logic_rel_typing Γ b₀ b₁ τ𝕒 →
    logic_rel_typing ((τ𝕒, 𝟙) :: Γ) ({0 ↦ Γ.length} e₀) ({0 ↦ Γ.length} e₁) τ𝕓 →
    logic_rel_typing Γ (.lets b₀ e₀) (.lets b₁ e₁) τ𝕓 :=
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
  intros k γ₀ γ₁ HsemΓ
  rw [logic_rel_expr]
  intros j Hindex v₀ Hvalue₀ Hstep₀
  simp at Hstep₀
  have ⟨i₀, i₁, bv₀, HEqj, HvalueB₀, HstepB₀, HstepHead₀⟩ := pure_stepn_indexed.refine.lets _ _ _ _ Hvalue₀ Hstep₀
  have Hb := Hb _ _ _ HsemΓ
  rw [logic_rel_expr] at Hb
  have ⟨bv₁, HstepB₁, Hsem_valueB⟩ := Hb i₀ (by omega) _ HvalueB₀ HstepB₀
  admit
