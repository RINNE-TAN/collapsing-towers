import CollapsingTowers.TwoLevelMut.LogicalEquiv.LogicalRelation

-- Γ ⊧ x ≈𝑙𝑜𝑔 x : Γ(x) ! ∅
lemma compatibility.fvar :
  ∀ Γ x τ,
    binds x (τ, 𝟚) Γ →
    wbt 𝟚 τ →
    log_equiv Γ (.fvar x) (.fvar x) τ ∅ :=
  by
  intros Γ x τ Hbinds Hwbt
  constructor; apply typing.fvar; apply Hbinds; apply Hwbt
  constructor; apply typing.fvar; apply Hbinds; apply Hwbt
  intros 𝓦 γ₀ γ₁ HsemΓ
  simp only [log_equiv_expr]
  intros σ₀ σ₁ Hsem_store
  exists 𝓦, σ₀, σ₁, msubst γ₀ (.fvar x), msubst γ₁ (.fvar x)
  constructor; apply World.future.refl
  constructor; apply stepn.refl
  constructor; apply stepn.refl
  constructor; apply Hsem_store
  apply log_equiv_env.binds_log_equiv_value _ _ _ _ _ _ HsemΓ Hbinds
