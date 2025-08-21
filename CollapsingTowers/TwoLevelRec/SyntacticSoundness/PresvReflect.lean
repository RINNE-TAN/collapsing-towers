import CollapsingTowers.TwoLevelRec.SyntacticSoundness.PresvCtx

lemma preservation.reflect :
  ∀ Γ E e τ φ,
    ctx𝔼 E →
    typing_reification Γ E⟦.reflect e⟧ (.rep τ) φ →
    typing_reification Γ (.lets𝕔 e E⟦.code (.bvar 0)⟧) (.rep τ) ⊥ :=
  by
  intros Γ E e τ φ HE Hτ
  admit

lemma preservation.reify :
  ∀ Γ intro R E e τ φ,
    ctxℝ intro Γ.length R →
    ctx𝔼 E →
    lc e →
    typing Γ 𝟚 R⟦E⟦.reflect e⟧⟧ τ φ →
    typing Γ 𝟚 R⟦(.lets𝕔 e E⟦.code (.bvar 0)⟧)⟧ τ φ :=
  by
  intros Γ intro R E e τ φ HR HE Hlc Hτ
  have Hlcl : lc E⟦.reflect e⟧ := by apply lc.under_ctx𝔼; apply HE; apply Hlc
  have Hlcr : lc (.lets𝕔 e E⟦.code (.bvar 0)⟧) :=
    by
    constructor
    . apply Hlc
    . apply lc.under_ctx𝔼; apply HE; simp
  cases HR
  case lam𝕔 =>
    cases Hτ
    case lam𝕔 τ𝕒 τ𝕓 _ Hwbt HX Hclosed =>
      rw [identity.opening_closing _ _ _ Hlcl] at HX
      apply typing.lam𝕔
      . rw [identity.opening_closing _ _ _ Hlcr]
        apply preservation.reflect _ _ _ _ _ HE HX
      . apply Hwbt
      . rw [← closed.under_closing]; constructor
        . apply closed.decompose_ctx𝔼 _ (.reflect e); apply HE
          apply typing_reification.closed_at_env _ _ _ _ HX
        . apply closed.under_ctx𝔼; apply HE
          apply typing_reification.closed_at_env _ _ _ _ HX
          simp
  case lets𝕔 => admit
  case run => admit
  case ifzl₂ => admit
  case ifzr₂ => admit
