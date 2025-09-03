import CollapsingTowers.TwoLevelMut.LogicalEquiv.LogicalRelation

-- Γ ⊧ x ≈𝑙𝑜𝑔 x : Γ(x)
lemma compatibility.fvar :
  ∀ Γ x τ,
    binds x (τ, 𝟚) Γ →
    wbt 𝟚 τ →
    log_equiv Γ (.fvar x) (.fvar x) τ :=
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

-- Γ ⊧ n ≈𝑙𝑜𝑔 n : ℕ
lemma compatibility.lit :
  ∀ Γ n,
    log_equiv Γ (.lit n) (.lit n) .nat :=
  by
  intros _ n
  constructor; apply typing.lit
  constructor; apply typing.lit
  intros 𝓦 γ₀ γ₁ HsemΓ
  simp only [log_equiv_expr]
  intros σ₀ σ₁ Hsem_store
  exists 𝓦, σ₀, σ₁, .lit n, .lit n
  constructor; apply World.future.refl
  constructor; simp; apply stepn.refl
  constructor; simp; apply stepn.refl
  constructor; apply Hsem_store
  simp

-- Γ ⊧ () ≈𝑙𝑜𝑔 () : unit
lemma compatibility.unit :
  ∀ Γ,
    log_equiv Γ .unit .unit .unit :=
  by
  intros n
  constructor; apply typing.unit
  constructor; apply typing.unit
  intros 𝓦 γ₀ γ₁ HsemΓ
  simp only [log_equiv_expr]
  intros σ₀ σ₁ Hsem_store
  exists 𝓦, σ₀, σ₁, .unit, .unit
  constructor; apply World.future.refl
  constructor; simp; apply stepn.refl
  constructor; simp; apply stepn.refl
  constructor; apply Hsem_store
  simp

-- Γ ⊧ f₀ ≈𝑙𝑜𝑔 f₁ : τ𝕒 → τ𝕓
-- Γ ⊧ arg₀ ≈𝑙𝑜𝑔 arg₁ : τ𝕒
-- —————————————————————————————————
-- Γ ⊧ f₀ @ arg₀ ≈𝑙𝑜𝑔 f₁ @ arg₁ : τ𝕓
lemma compatibility.app₁ :
  ∀ Γ f₀ f₁ arg₀ arg₁ τ𝕒 τ𝕓,
    log_equiv Γ f₀ f₁ (.arrow τ𝕒 τ𝕓 ⊥) →
    log_equiv Γ arg₀ arg₁ τ𝕒 →
    log_equiv Γ (.app₁ f₀ arg₀) (.app₁ f₁ arg₁) τ𝕓 :=
  by
  intros Γ f₀ f₁ arg₀ arg₁ τ𝕒 τ𝕓 Hf Harg
  have ⟨HτFun₀, HτFun₁, Hf⟩ := Hf
  have ⟨HτArg₀, HτArg₁, Harg⟩ := Harg
  have Hτ₀ : typing ϵ Γ 𝟚 (.app₁ f₀ arg₀) τ𝕓 ⊥ :=
    by
    rw [← Effect.union_pure ⊥, ← Effect.union_pure (⊥ ∪ ⊥)]
    apply typing.app₁; apply HτFun₀; apply HτArg₀
  have Hτ₁ : typing ϵ Γ 𝟚 (.app₁ f₁ arg₁) τ𝕓 ⊥ :=
    by
    rw [← Effect.union_pure ⊥, ← Effect.union_pure (⊥ ∪ ⊥)]
    apply typing.app₁; apply HτFun₁; apply HτArg₁
  constructor; apply Hτ₀
  constructor; apply Hτ₁
  intros 𝓦₀ γ₀ γ₁ HsemΓ
  simp only [log_equiv_expr]
  intros σ₀ σ₁ Hsem_store
  --
  --
  -- Γ ⊧ f₀ ≈𝑙𝑜𝑔 f₁ : τ𝕒 → τ𝕓
  -- ————————————————————————————
  -- 𝓦₁ ⊒ 𝓦₀
  -- ⟨σ₀, γ₀(f₀)⟩ ⇝* ⟨σ₂, fv₀⟩
  -- ⟨σ₁, γ₁(f₁)⟩ ⇝* ⟨σ₃, fv₁⟩
  -- (σ₂, σ₃) : 𝓦₁
  -- (𝓦₁, fv₀, fv₁) ∈ 𝓥⟦τ𝕒 → τ𝕓⟧
  simp only [log_equiv_expr] at Hf
  have ⟨𝓦₁, σ₂, σ₃, fv₀, fv₁, Hfuture₀, HstepFun₀, HstepFun₁, Hsem_store, Hsem_value_fun⟩ := Hf _ _ _ HsemΓ _ _ Hsem_store
  --
  --
  -- Γ ⊧ arg₀ ≈𝑙𝑜𝑔 arg₁ : τ𝕒
  -- ——————————————————————————————
  -- 𝓦₂ ⊒ 𝓦₁
  -- ⟨σ₂, γ₀(arg₀)⟩ ⇝* ⟨σ₄, argv₀⟩
  -- ⟨σ₃, γ₁(arg₁)⟩ ⇝* ⟨σ₅, argv₁⟩
  -- (σ₄, σ₅) : 𝓦₂
  -- (𝓦₂, argv₀, argv₁) ∈ 𝓥⟦τ𝕒⟧
  simp only [log_equiv_expr] at Harg
  have ⟨𝓦₂, σ₄, σ₅, argv₀, argv₁, Hfuture₁, HstepArg₀, HstepArg₁, Hsem_store, Hsem_value_arg⟩ := Harg 𝓦₁ _ _ (log_equiv_env.antimono _ _ _ _ _ HsemΓ Hfuture₀) _ _ Hsem_store
  --
  --
  -- (𝓦₁, fv₀, fv₁) ∈ 𝓥⟦τ𝕒 → τ𝕓⟧
  -- (𝓦₂, argv₀, argv₁) ∈ 𝓥⟦τ𝕒⟧
  -- ——————————————————————————————————————
  -- (𝓦₂, fv₀ @ argv₀, fv₁ @ argv₁) ∈ 𝓔⟦τ𝕓⟧
  have Hsem_expr := log_equiv_value.apply 𝓦₂ _ _ _ _ _ _ (log_equiv_value.antimono _ _ _ _ _ Hsem_value_fun Hfuture₁) Hsem_value_arg
  --
  --
  -- (𝓦₂, fv₀ @ argv₀, fv₁ @ argv₁) ∈ 𝓔⟦τ𝕓⟧
  -- ——————————————————————————————————————
  -- ⟨σ₄, fv₀ @ argv₀⟩ ⇝* ⟨σ₆, v₀⟩
  -- ⟨σ₅, fv₁ @ argv₁⟩ ⇝* ⟨σ₇, v₁⟩
  simp only [log_equiv_expr] at Hsem_expr
  have ⟨𝓦₃, σ₆, σ₇, v₀, v₁, Hfuture₂, Hstep₀, Hstep₁, Hsem_store, Hsem_value⟩ := Hsem_expr _ _ Hsem_store
  exists 𝓦₃, σ₆, σ₇, v₀, v₁
  constructor
  . apply World.future.trans _ _ _ Hfuture₂
    apply World.future.trans _ _ _ Hfuture₁
    apply Hfuture₀
  constructor
  --
  --
  -- ⟨σ₀, γ₀(f₀)⟩ ⇝* ⟨σ₂, fv₀⟩
  -- ⟨σ₂, γ₀(arg₀)⟩ ⇝* ⟨σ₄, argv₀⟩
  -- ⟨σ₄, fv₀ @ argv₀⟩ ⇝* ⟨σ₆, v₀⟩
  -- ————————————————————————————————————
  -- ⟨σ₀, γ₀(f₀) @ γ₀(arg₀)⟩ ⇝* ⟨σ₆, v₀⟩
  . admit
  constructor
  . admit
  constructor
  . apply Hsem_store
  . apply Hsem_value
