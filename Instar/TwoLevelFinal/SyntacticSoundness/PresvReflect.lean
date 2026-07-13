import Instar.TwoLevelFinal.SyntacticSoundness.PresvCtx

theorem preservation.reflect.head :
  ∀ Γ E e τ ε,
    ctx𝔼 E →
    typing_reification Γ E⟦.reflect e⟧ τ ε →
    typing_reification Γ (.lets𝕔 e E⟦.code (.bvar 0)⟧) τ ⊥ :=
  by
  intros Γ E e τ ε HE Hτ
  cases Hτ
  case pure Hτ =>
    have ⟨τ𝕖, ε₀, ε₁, HEqε, Hτr, HτE⟩ := preservation.under_ctx𝔼 _ _ _ _ _ HE Hτ
    cases Hτr; simp at HEqε
  case reify Hτ =>
    have ⟨τ𝕖, ε₀, ε₁, HEqε, Hτr, HτE⟩ := preservation.under_ctx𝔼 _ _ _ _ _ HE Hτ
    cases Hτr
    case reflect τ𝕖 Hτe =>
      have ⟨Hwbt, _⟩ := typing.dynamic_impl_pure _ _ _ _ Hτe
      apply typing_reification.pure
      apply typing.lets𝕔
      . apply Hτe
      . simp [opening.under_ctx𝔼 _ _ _ _ HE]
        apply typing_reification.reify
        apply HτE [(τ𝕖, 𝟚)]
        apply typing.code_fragment; simp; apply Hwbt
      . apply Hwbt
      . apply closed.under_ctx𝔼; apply HE
        apply typing.closed_at_env _ _ _ _ _ Hτ
        simp

theorem preservation.reflect :
  ∀ Γ Q E e τ ε,
    ctxℚ Γ.length Q →
    ctx𝔼 E →
    lc e →
    typing Γ 𝟙 Q⟦E⟦.reflect e⟧⟧ τ ε →
    typing Γ 𝟙 Q⟦.lets𝕔 e E⟦.code (.bvar 0)⟧⟧ τ ε :=
  by
  intros Γ Q E e τ ε HQ HE Hlc Hτ
  generalize HEqlvl : Γ.length = lvl
  rw [HEqlvl] at HQ
  induction HQ generalizing Γ τ ε
  case holeℝ R HR =>
    have Hlc : lc E⟦.reflect e⟧ := lc.under_ctx𝔼 _ _ _ HE Hlc
    have Hsf : store_free E⟦.reflect e⟧ → store_free (.lets𝕔 e E⟦.code (.bvar 0)⟧) :=
      by
      intros HsfE
      constructor
      . apply store_free.decompose_ctx𝔼 _ _ HE HsfE
      . apply store_free.under_ctx𝔼 _ _ _ HE HsfE (by simp)
    have Hfv : fv (.lets𝕔 e E⟦.code (.bvar 0)⟧) ⊆ fv E⟦.reflect e⟧ :=
      by
      simp; constructor
      . apply fv.decompose_ctx𝔼 _ (.reflect e) HE
      . apply fv.under_ctx𝔼; apply HE; simp
    rw [← HEqlvl] at HR
    have ⟨Δ, τ𝕖, ε₁, HEqΓ, Hτ, IHτR⟩ := preservation.under_ctxℝ _ _ _ _ _ _ HR Hlc Hτ
    apply IHτR _ _ Hsf Hfv (preservation.reflect.head _ _ _ _ _ HE Hτ)
  case cons𝔹 B Q HB HQ IH =>
    have ⟨τ𝕖, ε₀, ε₁, HEqε, Hτ, IHτB⟩ := preservation.under_ctx𝔹 _ _ _ _ _ HB Hτ
    rw [HEqε]
    apply IHτB ⦰
    apply IH _ _ _ Hτ HEqlvl
  case consℝ R Q HR HQ IH =>
    rw [← HEqlvl] at HR IH
    rw [← ctx_comp R Q]
    have Hlc : lc Q⟦E⟦.reflect e⟧⟧ :=
      by
      apply lc.under_ctxℚ; apply HQ
      apply lc.under_ctx𝔼; apply HE
      apply Hlc
    have Hsf : store_free Q⟦E⟦.reflect e⟧⟧ → store_free Q⟦.lets𝕔 e E⟦.code (.bvar 0)⟧⟧ :=
      by
      intros HsfQ
      apply store_free.under_ctxℚ _ _ _ _ HQ HsfQ
      have HsfE := store_free.decompose_ctxℚ _ _ _ HQ HsfQ
      constructor
      . apply store_free.decompose_ctx𝔼 _ _ HE HsfE
      . apply store_free.under_ctx𝔼 _ _ _ HE HsfE (by simp)
    have Hfv : fv Q⟦.lets𝕔 e E⟦.code (.bvar 0)⟧⟧ ⊆ fv Q⟦E⟦.reflect e⟧⟧ :=
      by
      apply fv.under_ctxℚ; apply HQ
      simp; constructor
      . apply fv.decompose_ctx𝔼 _ (.reflect e) HE
      . apply fv.under_ctx𝔼; apply HE; simp
    have ⟨Δ, τ𝕖, ε₁, HEqΓ, Hτ, IHτR⟩ := preservation.under_ctxℝ _ _ _ _ _ _ HR Hlc Hτ
    cases Hτ
    case pure Hτ =>
      have Hτ := IH _ _ _ Hτ HEqΓ
      apply IHτR _ _ Hsf Hfv (typing_reification.pure _ _ _ Hτ)
    case reify Hτ =>
      have Hτ := IH _ _ _ Hτ HEqΓ
      apply IHτR _ _ Hsf Hfv (typing_reification.reify _ _ _ _ Hτ)
