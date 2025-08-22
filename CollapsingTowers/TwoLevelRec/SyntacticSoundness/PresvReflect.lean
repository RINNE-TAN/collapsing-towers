import CollapsingTowers.TwoLevelRec.SyntacticSoundness.PresvCtx

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
  case holeℝ => admit
  case cons𝔹 B Q HB HQ IH =>
    rw [← ctx_comp B Q]
    apply preservation.under_ctx𝔹
    . apply HB
    . intro _ _ Hτ; apply IH; apply Hτ; simp [HEqlvl]
    . apply Hτ
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
