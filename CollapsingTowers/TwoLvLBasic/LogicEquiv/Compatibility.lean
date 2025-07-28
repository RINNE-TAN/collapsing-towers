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
