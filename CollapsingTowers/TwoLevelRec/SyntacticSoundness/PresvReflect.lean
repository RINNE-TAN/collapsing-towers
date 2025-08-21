import CollapsingTowers.TwoLevelRec.SyntacticSoundness.PresvCtx

lemma preservation.reflect :
  ∀ Γ E e τ φ,
    ctx𝔼 E →
    typing Γ 𝟚 (E (.reflect e)) τ φ →
    typing Γ 𝟚 (.lets𝕔 e (E (.code (.bvar 0)))) τ ⊥ :=
  by
  intros Γ E e τ φ HE Hτ
  have ⟨τ𝕖, φ₀, φ₁, HEqφ, Hτr, HτE⟩ := preservation.under_ctx𝔼 _ _ _ _ _ HE Hτ
  cases Hτr
  case reflect Hτe =>
    admit
