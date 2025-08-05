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
