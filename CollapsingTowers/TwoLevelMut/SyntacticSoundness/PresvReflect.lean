import CollapsingTowers.TwoLevelMut.SyntacticSoundness.PresvCtx

theorem preservation.reflect.head :
  ∀ σ Γ E e τ φ ω,
    ctx𝔼 E →
    typing_reification σ Γ E⟦.reflect e⟧ τ φ ω →
    typing_reification σ Γ (.lets𝕔 e E⟦.code (.bvar 0)⟧) τ ⊥ ω :=
  by
  intros σ Γ E e τ φ ω HE Hτ
  cases Hτ
  case pure Hτ =>
    have ⟨τ𝕖, φ₀, φ₁, ω₀, ω₁, HEqφ, HEqω, Hτr, IHτE⟩ := preservation.under_ctx𝔼 _ _ _ _ _ _ _ HE Hτ
    cases Hτr; simp at HEqφ
  case reify Hτ =>
    have ⟨τ𝕖, φ₀, φ₁, ω₀, ω₁, HEqφ, HEqω, Hτr, IHτE⟩ := preservation.under_ctx𝔼 _ _ _ _ _ _ _ HE Hτ
    cases Hτr
    case reflect τ𝕖 Hτe =>
      have ⟨Hwbt, _, _⟩ := typing.dynamic_impl_pure _ _ _ _ _ _ Hτe
      rw [HEqω]
      apply typing_reification.pure
      apply typing.lets𝕔
      . apply Hτe
      . simp [opening.under_ctx𝔼 _ _ _ _ HE]
        rw [← Set.empty_union ω₁]
        apply typing_reification.reify
        apply IHτE _ [(τ𝕖, 𝟚)] _ _ _ (by omega)
        apply typing.code_fragment; simp; apply Hwbt
      . apply Hwbt
      . apply closed.under_ctx𝔼; apply HE
        apply typing.closed_at_env _ _ _ _ _ _ _ Hτ
        simp

theorem preservation.reflect :
  ∀ σ Γ Q E e τ φ ω₀,
    ctxℚ Γ.length Q →
    ctx𝔼 E →
    lc e →
    typing σ Γ 𝟙 Q⟦E⟦.reflect e⟧⟧ τ φ ω₀ →
    ∃ ω₁,
      typing σ Γ 𝟙 Q⟦.lets𝕔 e E⟦.code (.bvar 0)⟧⟧ τ φ ω₁ ∧
      ω₁ ≤ ω₀ ∧
      stage_meffects 𝟙 (ω₀ \ ω₁) :=
  by
  intros σ Γ Q E e τ φ ω₀ HQ HE Hlc Hτ
  generalize HEqlvl : Γ.length = lvl
  rw [HEqlvl] at HQ
  induction HQ generalizing Γ τ φ ω₀
  case holeℝ R HR =>
    have Hlc : lc E⟦.reflect e⟧ := lc.under_ctx𝔼 _ _ _ HE Hlc
    have Hfv : fv (.lets𝕔 e E⟦.code (.bvar 0)⟧) ⊆ fv E⟦.reflect e⟧ :=
      by
      simp; constructor
      . apply fv.decompose_ctx𝔼 _ (.reflect e) HE
      . apply fv.under_ctx𝔼; apply HE; simp
    rw [← HEqlvl] at HR
    have ⟨Δ, τ𝕖, φ₁, ω₁, HEqΓ, Hτ, IHτR⟩ := preservation.under_ctxℝ _ _ _ _ _ _ _ _ HR Hlc Hτ
    have ⟨ω₂, HLeω, Hdiffω, Hτ⟩ := IHτR σ _ _ ω₁ (by omega) Hfv (by simp) (by simp) (preservation.reflect.head _ _ _ _ _ _ _ HE Hτ)
    exists ω₂
  case cons𝔹 B Q HB HQ IH =>
    have ⟨τ𝕖, φ₁, φ₂, ω₁, ω₂, HEqφ, HEqω, Hτ, IHτB⟩ := preservation.under_ctx𝔹 _ _ _ _ _ _ _ HB Hτ
    rw [HEqφ, HEqω]
    have ⟨ω₃, Hτ, HLeω, Hdiffω⟩ := IH _ _ _ _ Hτ HEqlvl
    have Hτ := IHτB σ ⦰ _ _ _ (by omega) Hτ
    exists ω₃ ∪ ω₂; constructor
    . apply Hτ
    . constructor; apply Set.union_subset_union_left _ HLeω
      apply stage_meffects.mono _ _ _ _ Hdiffω
      apply Set.union_diff_union_cancel_right
  case consℝ R Q HR HQ IH =>
    rw [← HEqlvl] at HR IH
    rw [← ctx_comp R Q]
    have Hlc : lc Q⟦E⟦.reflect e⟧⟧ :=
      by
      apply lc.under_ctxℚ; apply HQ
      apply lc.under_ctx𝔼; apply HE
      apply Hlc
    have Hfv : fv Q⟦.lets𝕔 e E⟦.code (.bvar 0)⟧⟧ ⊆ fv Q⟦E⟦.reflect e⟧⟧ :=
      by
      apply fv.under_ctxℚ; apply HQ
      simp; constructor
      . apply fv.decompose_ctx𝔼 _ (.reflect e) HE
      . apply fv.under_ctx𝔼; apply HE; simp
    have ⟨Δ, τ𝕖, φ₁, ω₁, HEqΓ, Hτ, IHτR⟩ := preservation.under_ctxℝ _ _ _ _ _ _ _ _ HR Hlc Hτ
    cases Hτ
    case pure Hτ =>
      have ⟨ω₂, Hτ, HLeω, Hdiffω⟩ := IH _ _ _ _ Hτ HEqΓ
      have ⟨ω₃, HLeω, Hdiffω, Hτ⟩ := IHτR σ _ _ _ (by simp) Hfv HLeω Hdiffω (typing_reification.pure _ _ _ _ _ Hτ)
      exists ω₃
    case reify Hτ =>
      have ⟨ω₂, Hτ, HLeω, Hdiffω⟩ := IH _ _ _ _ Hτ HEqΓ
      have ⟨ω₃, HLeω, Hdiffω, Hτ⟩ := IHτR σ _ _ _ (by simp) Hfv HLeω Hdiffω (typing_reification.reify _ _ _ _ _ _ Hτ)
      exists ω₃
