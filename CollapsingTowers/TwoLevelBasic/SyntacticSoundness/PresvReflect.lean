import CollapsingTowers.TwoLevelBasic.SyntacticSoundness.PresvCtx

lemma preservation.reflect.head :
  ∀ Γ E e τ φ,
    ctx𝔼 E →
    typing_reification Γ E⟦.reflect e⟧ τ φ →
    typing_reification Γ (.lets𝕔 e E⟦.code (.bvar 0)⟧) τ ⊥ :=
  by
  intros Γ E e τ φ HE Hτ
  cases Hτ
  case pure Hτ =>
    have ⟨τ𝕖, φ₀, φ₁, HEqφ, Hτr, HτE⟩ := preservation.under_ctx𝔼 _ _ _ _ _ HE Hτ
    cases Hτr; simp at HEqφ
  case reify Hτ =>
    have ⟨τ𝕖, φ₀, φ₁, HEqφ, Hτr, HτE⟩ := preservation.under_ctx𝔼 _ _ _ _ _ HE Hτ
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

lemma preservation.reflect :
  ∀ Γ Q E e τ φ,
    ctxℚ Γ.length Q →
    ctx𝔼 E →
    lc e →
    typing Γ 𝟙 Q⟦E⟦.reflect e⟧⟧ τ φ →
    typing Γ 𝟙 Q⟦.lets𝕔 e E⟦.code (.bvar 0)⟧⟧ τ φ :=
  by
  intros Γ Q E e τ φ HQ HE Hlc Hτ
  generalize HEqlvl : Γ.length = lvl
  rw [HEqlvl] at HQ
  induction HQ generalizing Γ τ φ
  case holeℝ R HR =>
    have Hlc : lc E⟦.reflect e⟧ := lc.under_ctx𝔼 _ _ _ HE Hlc
    have Hfv : fv (.lets𝕔 e E⟦.code (.bvar 0)⟧) ⊆ fv E⟦.reflect e⟧ :=
      by
      simp; constructor
      . apply fv.decompose_ctx𝔼 _ (.reflect e) HE
      . apply fv.under_ctx𝔼; apply HE; simp
    rw [← HEqlvl] at HR
    cases HR
    cases Hτ
    case lam𝕔 Hwbt HX Hclosed =>
      rw [identity.opening_closing _ _ _ Hlc] at HX
      have HX := preservation.reflect.head _ _ _ _ _ HE HX
      apply typing.lam𝕔
      . rw [identity.opening_closing _ _ _ (typing_reification.regular _ _ _ _ HX)]
        apply HX
      . apply Hwbt
      . rw [← closed.under_closing]
        apply typing_reification.closed_at_env _ _ _ _ HX
    case lets𝕔 =>
      cases Hτ
      case lets𝕔 Hwbt Hb HX Hclosed =>
        rw [identity.opening_closing _ _ _ Hlc] at HX
        have HX := preservation.reflect.head _ _ _ _ _ HE HX
        apply typing.lets𝕔
        . apply Hb
        . rw [identity.opening_closing _ _ _ (typing_reification.regular _ _ _ _ HX)]
          apply HX
        . apply Hwbt
        . rw [← closed.under_closing]
          apply typing_reification.closed_at_env _ _ _ _ HX
    case run =>
      cases Hτ
      case run Hclosed HX =>
        have HX := preservation.reflect.head _ _ _ _ _ HE HX
        apply typing.run
        . apply HX
        . rw [closed_iff_fv_empty] at Hclosed
          simp [Hclosed] at Hfv
          rw [closed_iff_fv_empty]
          simp [Hfv]
  case cons𝔹 B Q HB HQ IH =>
    have ⟨τ𝕖, φ₀, φ₁, HEqφ, Hτ, IHτB⟩ := preservation.under_ctx𝔹 _ _ _ _ _ HB Hτ
    rw [HEqφ]
    apply IHτB ⦰
    apply IH _ _ _ Hτ HEqlvl
  case consℝ R Q HR HQ IH =>
    rw [← HEqlvl] at HR
    rw [← ctx_comp R Q]
    apply preservation.under_ctxℝ _ _ _ Q⟦E⟦.reflect e⟧⟧ Q⟦.lets𝕔 e E⟦.code (.bvar 0)⟧⟧
    . apply HR
    . apply lc.under_ctxℚ; apply HQ
      apply lc.under_ctx𝔼; apply HE
      apply Hlc
    . apply fv.under_ctxℚ; apply HQ
      simp; constructor
      . apply fv.decompose_ctx𝔼 _ (.reflect e) HE
      . apply fv.under_ctx𝔼; apply HE; simp
    . intros _ _ _ _ Hτ; apply IH; apply Hτ; omega
    . apply Hτ
