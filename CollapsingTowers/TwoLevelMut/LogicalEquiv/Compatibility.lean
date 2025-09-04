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
  have ⟨Hmwf₀, Hmwf₁⟩ := log_equiv_env.syntactic.mwf _ _ _ _ HsemΓ
  have ⟨HmG₀, HmG₁⟩ := log_equiv_env.syntactic.mgrounded _ _ _ _ HsemΓ
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
  have ⟨HvalueFun₀, HvalueFun₁⟩ := log_equiv_value.syntactic.value _ _ _ _ Hsem_value_fun
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
  . simp
    -- left
    apply stepn.trans
    apply stepn_grounded.congruence_under_ctx𝔹 _ _ _ _ _ (ctx𝔹.appl₁ _ _) _ HstepFun₀
    . apply lc.under_msubst _ _ _ Hmwf₀ (typing.regular _ _ _ _ _ _ HτArg₀)
    . apply grounded.under_msubst _ _ HmG₀ (typing.dynamic_impl_grounded _ _ _ _ _ HτFun₀)
    -- right
    apply stepn.trans
    apply stepn_grounded.congruence_under_ctx𝔹 _ _ _ _ _ (ctx𝔹.appr₁ _ _) _ HstepArg₀
    . apply HvalueFun₀
    . apply grounded.under_msubst _ _ HmG₀ (typing.dynamic_impl_grounded _ _ _ _ _ HτArg₀)
    -- head
    apply Hstep₀
  constructor
  --
  --
  -- ⟨σ₁, γ₀(f₁)⟩ ⇝* ⟨σ₃, fv₁⟩
  -- ⟨σ₃, γ₁(arg₁)⟩ ⇝* ⟨σ₅, argv₁⟩
  -- ⟨σ₅, fv₁ @ argv₁⟩ ⇝* ⟨σ₇, v₁⟩
  -- ————————————————————————————————————
  -- ⟨σ₁, γ₁(f₁) @ γ₁(arg₁)⟩ ⇝* ⟨σ₇, v₁⟩
  . simp
    -- left
    apply stepn.trans
    apply stepn_grounded.congruence_under_ctx𝔹 _ _ _ _ _ (ctx𝔹.appl₁ _ _) _ HstepFun₁
    . apply lc.under_msubst _ _ _ Hmwf₁ (typing.regular _ _ _ _ _ _ HτArg₁)
    . apply grounded.under_msubst _ _ HmG₁ (typing.dynamic_impl_grounded _ _ _ _ _ HτFun₁)
    -- right
    apply stepn.trans
    apply stepn_grounded.congruence_under_ctx𝔹 _ _ _ _ _ (ctx𝔹.appr₁ _ _) _ HstepArg₁
    . apply HvalueFun₁
    . apply grounded.under_msubst _ _ HmG₁ (typing.dynamic_impl_grounded _ _ _ _ _ HτArg₁)
    -- head
    apply Hstep₁
  constructor
  . apply Hsem_store
  . apply Hsem_value

-- Γ ⊧ n₀ ≈𝑙𝑜𝑔 n₁ : ℕ
-- ——————————————————————————————————
-- Γ ⊧ alloc n₀ ≈𝑙𝑜𝑔 alloc n₁ : ref ℕ
lemma compatibility.alloc₁ :
  ∀ Γ n₀ n₁,
    log_equiv Γ n₀ n₁ .nat →
    log_equiv Γ (.alloc₁ n₀) (.alloc₁ n₁) (.ref .nat) :=
  by
  intros Γ n₀ n₁ He
  have ⟨HτNat₀, HτNat₁, He⟩ := He
  have Hτ₀ : typing ϵ Γ 𝟚 (.alloc₁ n₀) (.ref .nat) ⊥ :=
    by
    rw [← Effect.union_pure ⊥]
    apply typing.alloc₁; apply HτNat₀
  have Hτ₁ : typing ϵ Γ 𝟚 (.alloc₁ n₁) (.ref .nat) ⊥ :=
    by
    rw [← Effect.union_pure ⊥]
    apply typing.alloc₁; apply HτNat₁
  constructor; apply Hτ₀
  constructor; apply Hτ₁
  intros 𝓦₀ γ₀ γ₁ HsemΓ
  have ⟨HmG₀, HmG₁⟩ := log_equiv_env.syntactic.mgrounded _ _ _ _ HsemΓ
  simp only [log_equiv_expr]
  intros σ₀ σ₁ Hsem_store
  --
  --
  -- Γ ⊧ n₀ ≈𝑙𝑜𝑔 n₁ : ℕ
  -- ————————————————————————————
  -- 𝓦₁ ⊒ 𝓦₀
  -- ⟨σ₀, γ₀(n₀)⟩ ⇝* ⟨σ₂, nv₀⟩
  -- ⟨σ₁, γ₁(n₁)⟩ ⇝* ⟨σ₃, nv₁⟩
  -- (σ₂, σ₃) : 𝓦₁
  -- nv₀ = nv₁
  simp only [log_equiv_expr] at He
  have ⟨𝓦₁, σ₂, σ₃, nv₀, nv₁, Hfuture₀, HstepNat₀, HstepNat₁, Hsem_store, Hsem_value_nat⟩ := He _ _ _ HsemΓ _ _ Hsem_store
  have ⟨HvalueNat₀, HvalueNat₁⟩ := log_equiv_value.syntactic.value _ _ _ _ Hsem_value_nat
  cases HvalueNat₀ <;> try simp at Hsem_value_nat
  case lit nv₀ =>
  cases HvalueNat₁ <;> try simp at Hsem_value_nat
  case lit nv₁ =>
  exists World.ext 𝓦₁ σ₂.length σ₃.length, (.lit nv₀) :: σ₂, (.lit nv₁) :: σ₃, .loc σ₂.length, .loc σ₃.length
  constructor
  . apply World.future.trans _ _ _ (World.future.ext _ _ _) Hfuture₀
  constructor
  --
  --
  -- ⟨σ₀, γ₀(n₀)⟩ ⇝* ⟨σ₂, nv₀⟩
  -- —————————————————————————————————————————————————
  -- ⟨σ₀, alloc γ₀(n₀)⟩ ⇝* ⟨nv₀ :: σ₂, loc σ₂.length⟩
  . simp
    -- left
    apply stepn.trans
    apply stepn_grounded.congruence_under_ctx𝔹 _ _ _ _ _ ctx𝔹.alloc₁ _ HstepNat₀
    . apply grounded.under_msubst _ _ HmG₀ (typing.dynamic_impl_grounded _ _ _ _ _ HτNat₀)
    -- head
    apply stepn.multi _ _ _ _ (stepn.refl _)
    apply step_lvl.mutable _ _ _ _ _ ctx𝕄.hole
    . simp
    . apply head_mutable.alloc₁
  constructor
  --
  --
  -- ⟨σ₁, γ₁(n₁)⟩ ⇝* ⟨σ₃, nv₁⟩
  -- —————————————————————————————————————————————————
  -- ⟨σ₁, alloc γ₁(n₁)⟩ ⇝* ⟨nv₁ :: σ₃, loc σ₃.length⟩
  . simp
    -- left
    apply stepn.trans
    apply stepn_grounded.congruence_under_ctx𝔹 _ _ _ _ _ ctx𝔹.alloc₁ _ HstepNat₁
    . apply grounded.under_msubst _ _ HmG₁ (typing.dynamic_impl_grounded _ _ _ _ _ HτNat₁)
    -- head
    apply stepn.multi _ _ _ _ (stepn.refl _)
    apply step_lvl.mutable _ _ _ _ _ ctx𝕄.hole
    . simp
    . apply head_mutable.alloc₁
  constructor
  . rw [Hsem_value_nat]
    apply log_equiv_store.ext _ _ _ _ Hsem_store
  . simp
