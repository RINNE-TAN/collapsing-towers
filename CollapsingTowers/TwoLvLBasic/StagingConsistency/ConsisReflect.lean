import CollapsingTowers.TwoLvLBasic.StagingConsistency.ConsisCtx

-- Γ ⊢ E⟦reflect b⟧ : τ
-- ——————————————————————————————————————————————————————
-- ‖Γ‖ ⊨ ‖E⟦reflect b⟧‖ ≈ ‖let𝕔 x = b in ‖E⟦code x⟧‖ : ‖τ‖
theorem consistency.reflect :
  ∀ Γ E b τ φ,
    ctx𝔼 E →
    typing Γ 𝟙 E⟦.reflect b⟧ τ φ →
    logic_equiv_typing ‖Γ‖𝛾 ‖E⟦.reflect b⟧‖ (.lets ‖b‖ ‖E⟦.code (.bvar 0)⟧‖) ‖τ‖𝜏 :=
  by
  intros Γ E b τ φ HE Hτ
  have ⟨τ𝕖, φ₀, φ₁, HEqφ, Hτr, HτE⟩ := preservation.under_ctx𝔼 _ _ _ _ _ HE Hτ
  constructor; constructor
  . rw [lc, ← lc.under_erase]; apply typing.regular; apply Hτ
  . rw [← env.erase.length, ← closed.under_erase]; apply typing.closed_at_env; apply Hτ
  constructor; constructor
  . constructor
    . rw [← lc.under_erase]; apply typing.regular _ _ _ _ _ Hτr
    . rw [← lc.under_erase]; apply lc.under_ctx𝔼; apply HE; simp
  . constructor
    . simp [← env.erase.length, ← closed.under_erase]; apply typing.closed_at_env _ _ _ _ _ Hτr
    . simp [← env.erase.length, ← closed.under_erase]; apply closed.under_ctx𝔼; apply HE
      apply typing.closed_at_env _ _ _ _ _ Hτ; simp
  intros γ₀ γ₁ HsemΓ
  have ⟨Hmulti_wf₀, Hmulti_wf₁⟩ := logic_equiv_env.multi_wf _ _ _ HsemΓ
  have ⟨HEq₀, HEq₁⟩ := logic_equiv_env.length _ _ _ HsemΓ
  have ⟨τ𝕖, Hsem𝕖, Hsem𝔼⟩ := consistency.under_ctx𝔼 _ _ _ _ _ HE Hτ
  rw [logic_equiv_typing] at Hsem𝕖 Hsem𝔼
  have Hsem𝕖 := Hsem𝕖.right.right γ₀ γ₁ HsemΓ
  rw [logic_equiv_expr] at Hsem𝕖
  have ⟨v₀, v₁, Hstepv₀, Hstepv₁, Hsem_value⟩ := Hsem𝕖
  have ⟨Hvalue₀, Hvalue₁⟩ := logic_equiv_value.syntactic_value _ _ _ Hsem_value
  have ⟨Hwf₀, Hwf₁⟩ := logic_equiv_value.wf _ _ _ Hsem_value
  have Hsem𝔼 := Hsem𝔼.right.right (v₀ :: γ₀) (v₁ :: γ₁) (logic_equiv_env.cons _ _ _ _ _ _ Hsem_value HsemΓ)
  apply logic_equiv_expr.stepn; apply Hsem𝔼
  . have ⟨E, HE, HcloseE, IHγ⟩ := logic_equiv_env.erase_ctx𝔼 _ _ _ _ _ _ _ HE Hτ HsemΓ
    rw [multi_subst, ← comm.multi_subst_subst, IHγ, IHγ]
    simp [HEq₀, ← env.erase.length]
    rw [subst.under_ctx𝔼 _ _ _ _ _ HE HcloseE]
    apply pure_stepn.congruence_under_ctx𝔼 _ _ _ HE; simp; apply Hstepv₀
    rfl; apply Hwf₀.right; apply Hmulti_wf₀
  . simp
    -- left step
    apply pure_stepn.trans
    apply pure_stepn.congruence_under_ctx𝔹 _ _ _ (ctx𝔹.lets _ _) Hstepv₁
    apply lc.under_multi_subst; apply Hmulti_wf₁
    rw [← lc.under_erase]; apply lc.under_ctx𝔼; apply HE; simp
    -- head step
    apply pure_stepn.multi _ _ _ _ (pure_stepn.refl _)
    have HEq :
      opening 0 v₁ (multi_subst γ₁ ‖E⟦.code (.bvar 0)⟧‖) =
      multi_subst γ₁ (subst γ₁.length v₁ ‖E⟦.fvar Γ.length⟧‖) :=
      by
        rw [← comm.multi_subst_subst, ← intros.subst γ₁.length]
        rw [← comm.multi_subst_opening, ← comm.erase_opening]
        rw [opening.under_ctx𝔼, erase.under_ctx𝔼]
        rw [HEq₁, ← env.erase.length]; rfl
        apply HE; apply HE; rfl; apply Hmulti_wf₁
        apply closed.inc
        apply closed.under_multi_subst; apply Hmulti_wf₁
        rw [HEq₁, ← env.erase.length, ← closed.under_erase]
        apply closed.under_ctx𝔼; apply HE
        apply typing.closed_at_env; apply Hτ; simp
        omega; omega; apply Hwf₁.right; apply Hmulti_wf₁
    rw [← HEq]; apply pure_step.pure id; apply ctx𝕄.hole
    constructor
    . apply lc.value; apply Hvalue₁
    . apply lc.under_multi_subst; apply Hmulti_wf₁
      rw [← lc.under_erase]
      apply lc.under_ctx𝔼; apply HE; simp
    apply head.lets; apply Hvalue₁
