import Instar.TwoLevelMut.LogicalEquiv.LogicalRelation

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
  intros
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

-- x ↦ τ𝕒, Γ ⊧ e₀ ≈𝑙𝑜𝑔 e₁ : τ𝕓
-- ——————————————————————————————
-- Γ ⊧ λx.e₀ ≈𝑙𝑜𝑔 λx.e₁ : τ𝕒 → τ𝕓
lemma compatibility.lam :
  ∀ Γ e₀ e₁ τ𝕒 τ𝕓,
    wbt 𝟚 τ𝕒 →
    closed_at e₀ Γ.length →
    closed_at e₁ Γ.length →
    log_equiv ((τ𝕒, 𝟚) :: Γ) ({0 ↦ Γ.length} e₀) ({0 ↦ Γ.length} e₁) τ𝕓 →
    log_equiv Γ (.lam e₀) (.lam e₁) (.arrow τ𝕒 τ𝕓 ⊥) :=
  by
  intros Γ e₀ e₁ τ𝕒 τ𝕓 Hwbt Hclosed₀ Hclosed₁ He
  have ⟨Hτ₀, Hτ₁, He⟩ := He
  have Hτ₀ : typing Γ 𝟚 (.lam e₀) (.arrow τ𝕒 τ𝕓 ⊥) ⊥ := by apply typing.lam; apply Hτ₀; apply Hwbt; apply Hclosed₀
  have Hτ₁ : typing Γ 𝟚 (.lam e₁) (.arrow τ𝕒 τ𝕓 ⊥) ⊥ := by apply typing.lam; apply Hτ₁; apply Hwbt; apply Hclosed₁
  constructor; apply Hτ₀
  constructor; apply Hτ₁
  intros 𝓦₀ γ₀ γ₁ HsemΓ
  have ⟨HEq₀, HEq₁⟩ := log_equiv_env.length _ _ _ _ HsemΓ
  have ⟨Hmwf₀, Hmwf₁⟩ := log_equiv_env.syntactic.mwf _ _ _ _ HsemΓ
  have ⟨HmG₀, HmG₁⟩ := log_equiv_env.syntactic.mgrounded _ _ _ _ HsemΓ
  simp only [log_equiv_expr]
  intros σ₀ σ₁ Hsem_store
  exists 𝓦₀, σ₀, σ₁, msubst γ₀ (.lam e₀), msubst γ₁ (.lam e₁)
  constructor; apply World.future.refl
  constructor; simp; apply stepn.refl
  constructor; simp; apply stepn.refl
  constructor; apply Hsem_store
  have Hwfe₀ : wf (.lam (msubst γ₀ e₀)) :=
    by
    constructor
    . apply lc.under_msubst _ _ _ Hmwf₀
      apply typing.regular _ _ _ _ _ Hτ₀
    . apply closed.under_msubst _ _ Hmwf₀
      simp [HEq₀, Hclosed₀]
  have Hwfe₁ : wf (.lam (msubst γ₁ e₁)) :=
    by
    constructor
    . apply lc.under_msubst _ _ _ Hmwf₁
      apply typing.regular _ _ _ _ _ Hτ₁
    . apply closed.under_msubst _ _ Hmwf₁
      simp [HEq₁, Hclosed₁]
  have HG₀ : grounded (.lam (msubst γ₀ e₀)) :=
    by
    apply grounded.under_msubst _ _ HmG₀
    apply typing.dynamic_impl_grounded _ _ _ _ Hτ₀
  have HG₁ : grounded (.lam (msubst γ₁ e₁)) :=
    by
    apply grounded.under_msubst _ _ HmG₁
    apply typing.dynamic_impl_grounded _ _ _ _ Hτ₁
  simp only [msubst.lam, log_equiv_value]
  constructor; apply Hwfe₀
  constructor; apply HG₀
  constructor; apply Hwfe₁
  constructor; apply HG₁
  intros 𝓦₁ argv₀ argv₁ Hfuture₀ Hsem_value_arg
  have ⟨HwfArg₀, HwfArg₁⟩ := log_equiv_value.syntactic.wf _ _ _ _ Hsem_value_arg
  have ⟨HvalueArg₀, HvalueArg₁⟩ := log_equiv_value.syntactic.value _ _ _ _ Hsem_value_arg
  simp only [log_equiv_expr]
  intros σ₂ σ₃ Hsem_store
  --
  --
  -- (𝓦₁, (x ↦ argv₀, γ₀)(e₀), (x ↦ argv₁, γ₁)(e₁)) ∈ 𝓔⟦τ𝕓⟧
  -- ————————————————————————————————————————————————————————
  -- ⟨σ₂, (x ↦ argv₀, γ₀)(e₀)⟩ ⭢* ⟨σ₄, v₀⟩
  -- ⟨σ₃, (x ↦ argv₁, γ₁)(e₁)⟩ ⭢* ⟨σ₅, v₁⟩
  -- (σ₄, σ₅) : 𝓦₂
  -- (𝓦₂, v₀, v₁) ∈ 𝓥⟦τ𝕓⟧
  have HsemΓ := log_equiv_env.cons _ _ _ _ _ _ _ Hsem_value_arg (log_equiv_env.antimono _ _ _ _ _ HsemΓ Hfuture₀)
  simp only [log_equiv_expr] at He
  have ⟨𝓦₂, σ₄, σ₅, v₀, v₁, Hfuture₁, Hstep₀, Hstep₁, Hsem_store, Hsem_value⟩ := He _ _ _ HsemΓ _ _ Hsem_store
  exists 𝓦₂, σ₄, σ₅, v₀, v₁
  constructor
  . apply Hfuture₁
  constructor
  -- ⟨σ₂, (x ↦ argv₀, γ₀)(e₀)⟩ ⭢* ⟨σ₄, v₀⟩
  -- ——————————————————————————————————————
  -- ⟨σ₂, λx.e₀ @ argv₀⟩ ⭢* ⟨σ₄, v₀⟩
  . have HEqSubst₀ : opening 0 argv₀ (msubst γ₀ e₀) = msubst (argv₀ :: γ₀) ({0 ↦ Γ.length} e₀) :=
      by
      rw [msubst, ← comm.msubst_subst _ _ _ _ (by omega) _ Hmwf₀]
      rw [comm.msubst_opening _ _ _ _ (by omega) Hmwf₀]
      rw [HEq₀, intro.subst]
      apply closed.inc; apply Hwfe₀.right; omega
      apply HwfArg₀.right
    rw [← HEqSubst₀] at Hstep₀
    apply stepn.multi _ _ _ _ Hstep₀
    apply step_lvl.pure _ _ _ _ ctx𝕄.hole
    . constructor; apply Hwfe₀.left; apply HwfArg₀.left
    . apply head_pure.app₁; apply HvalueArg₀
  constructor
  -- ⟨σ₃, (x ↦ argv₁, γ₁)(e₁)⟩ ⭢* ⟨σ₅, v₁⟩
  -- ——————————————————————————————————————
  -- ⟨σ₃, λx.e₁ @ argv₁⟩ ⭢* ⟨σ₅, v₁⟩
  . have HEqSubst₁ : opening 0 argv₁ (msubst γ₁ e₁) = msubst (argv₁ :: γ₁) ({0 ↦ Γ.length} e₁) :=
      by
      rw [msubst, ← comm.msubst_subst _ _ _ _ (by omega) _ Hmwf₁]
      rw [comm.msubst_opening _ _ _ _ (by omega) Hmwf₁]
      rw [HEq₁, intro.subst]
      apply closed.inc; apply Hwfe₁.right; omega
      apply HwfArg₁.right
    rw [← HEqSubst₁] at Hstep₁
    apply stepn.multi _ _ _ _ Hstep₁
    apply step_lvl.pure _ _ _ _ ctx𝕄.hole
    . constructor; apply Hwfe₁.left; apply HwfArg₁.left
    . apply head_pure.app₁; apply HvalueArg₁
  constructor
  . apply Hsem_store
  . apply Hsem_value

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
  have Hτ₀ : typing Γ 𝟚 (.app₁ f₀ arg₀) τ𝕓 ⊥ :=
    by
    rw [← Effect.union_pure ⊥, ← Effect.union_pure (⊥ ∪ ⊥)]
    apply typing.app₁; apply HτFun₀; apply HτArg₀
  have Hτ₁ : typing Γ 𝟚 (.app₁ f₁ arg₁) τ𝕓 ⊥ :=
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
  -- ⟨σ₀, γ₀(f₀)⟩ ⭢* ⟨σ₂, fv₀⟩
  -- ⟨σ₁, γ₁(f₁)⟩ ⭢* ⟨σ₃, fv₁⟩
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
  -- ⟨σ₂, γ₀(arg₀)⟩ ⭢* ⟨σ₄, argv₀⟩
  -- ⟨σ₃, γ₁(arg₁)⟩ ⭢* ⟨σ₅, argv₁⟩
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
  -- 𝓦₃ ⊒ 𝓦₂
  -- ⟨σ₄, fv₀ @ argv₀⟩ ⭢* ⟨σ₆, v₀⟩
  -- ⟨σ₅, fv₁ @ argv₁⟩ ⭢* ⟨σ₇, v₁⟩
  -- (σ₆, σ₇) : 𝓦₃
  -- (𝓦₃, v₀, v₁) ∈ 𝓥⟦τ𝕓⟧
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
  -- ⟨σ₀, γ₀(f₀)⟩ ⭢* ⟨σ₂, fv₀⟩
  -- ⟨σ₂, γ₀(arg₀)⟩ ⭢* ⟨σ₄, argv₀⟩
  -- ⟨σ₄, fv₀ @ argv₀⟩ ⭢* ⟨σ₆, v₀⟩
  -- ————————————————————————————————————
  -- ⟨σ₀, γ₀(f₀) @ γ₀(arg₀)⟩ ⭢* ⟨σ₆, v₀⟩
  . simp
    -- left
    apply stepn.trans
    apply stepn_grounded.congruence_under_ctx𝔹 _ _ _ _ _ (ctx𝔹.appl₁ _ _) _ HstepFun₀
    . apply lc.under_msubst _ _ _ Hmwf₀ (typing.regular _ _ _ _ _ HτArg₀)
    . apply grounded.under_msubst _ _ HmG₀ (typing.dynamic_impl_grounded _ _ _ _ HτFun₀)
    -- right
    apply stepn.trans
    apply stepn_grounded.congruence_under_ctx𝔹 _ _ _ _ _ (ctx𝔹.appr₁ _ _) _ HstepArg₀
    . apply HvalueFun₀
    . apply grounded.under_msubst _ _ HmG₀ (typing.dynamic_impl_grounded _ _ _ _ HτArg₀)
    -- head
    apply Hstep₀
  constructor
  --
  --
  -- ⟨σ₁, γ₀(f₁)⟩ ⭢* ⟨σ₃, fv₁⟩
  -- ⟨σ₃, γ₁(arg₁)⟩ ⭢* ⟨σ₅, argv₁⟩
  -- ⟨σ₅, fv₁ @ argv₁⟩ ⭢* ⟨σ₇, v₁⟩
  -- ————————————————————————————————————
  -- ⟨σ₁, γ₁(f₁) @ γ₁(arg₁)⟩ ⭢* ⟨σ₇, v₁⟩
  . simp
    -- left
    apply stepn.trans
    apply stepn_grounded.congruence_under_ctx𝔹 _ _ _ _ _ (ctx𝔹.appl₁ _ _) _ HstepFun₁
    . apply lc.under_msubst _ _ _ Hmwf₁ (typing.regular _ _ _ _ _ HτArg₁)
    . apply grounded.under_msubst _ _ HmG₁ (typing.dynamic_impl_grounded _ _ _ _ HτFun₁)
    -- right
    apply stepn.trans
    apply stepn_grounded.congruence_under_ctx𝔹 _ _ _ _ _ (ctx𝔹.appr₁ _ _) _ HstepArg₁
    . apply HvalueFun₁
    . apply grounded.under_msubst _ _ HmG₁ (typing.dynamic_impl_grounded _ _ _ _ HτArg₁)
    -- head
    apply Hstep₁
  constructor
  . apply Hsem_store
  . apply Hsem_value

-- Γ ⊧ b₀ ≈𝑙𝑜𝑔 b₁ : τ𝕒
-- x ↦ τ𝕒, Γ ⊧ e₀ ≈𝑙𝑜𝑔 e₁ : τ𝕓
-- —————————————————————————————————————————————————
-- Γ ⊧ lets x = b₀ in e₀ ≈𝑙𝑜𝑔 lets x = b₁ in e₁ : τ𝕓
lemma compatibility.lets :
  ∀ Γ b₀ b₁ e₀ e₁ τ𝕒 τ𝕓,
    wbt 𝟚 τ𝕒 →
    closed_at e₀ Γ.length →
    closed_at e₁ Γ.length →
    log_equiv Γ b₀ b₁ τ𝕒 →
    log_equiv ((τ𝕒, 𝟚) :: Γ) ({0 ↦ Γ.length} e₀) ({0 ↦ Γ.length} e₁) τ𝕓 →
    log_equiv Γ (.lets b₀ e₀) (.lets b₁ e₁) τ𝕓 :=
  by
  intros Γ b₀ b₁ e₀ e₁ τ𝕒 τ𝕓 Hwbt Hclosed₀ Hclosed₁ Hb He
  have ⟨Hτb₀, Hτb₁, Hb⟩ := Hb
  have ⟨Hτe₀, Hτe₁, He⟩ := He
  have Hτ₀ : typing Γ 𝟚 (.lets b₀ e₀) τ𝕓 ⊥ :=
    by
    rw [← Effect.union_pure ⊥]; apply typing.lets
    apply Hτb₀; apply Hτe₀; apply Hwbt; apply Hclosed₀
  have Hτ₁ : typing Γ 𝟚 (.lets b₁ e₁) τ𝕓 ⊥ :=
    by
    rw [← Effect.union_pure ⊥]; apply typing.lets
    apply Hτb₁; apply Hτe₁; apply Hwbt; apply Hclosed₁
  constructor; apply Hτ₀
  constructor; apply Hτ₁
  intros 𝓦₀ γ₀ γ₁ HsemΓ
  have ⟨HEq₀, HEq₁⟩ := log_equiv_env.length _ _ _ _ HsemΓ
  have ⟨Hmwf₀, Hmwf₁⟩ := log_equiv_env.syntactic.mwf _ _ _ _ HsemΓ
  have ⟨HmG₀, HmG₁⟩ := log_equiv_env.syntactic.mgrounded _ _ _ _ HsemΓ
  simp only [log_equiv_expr]
  intros σ₀ σ₁ Hsem_store
  --
  --
  -- Γ ⊧ b₀ ≈𝑙𝑜𝑔 b₁ : τ𝕒
  -- ——————————————————————————
  -- 𝓦₁ ⊒ 𝓦₀
  -- ⟨σ₀, γ₀(b₀)⟩ ⭢* ⟨σ₂, bv₀⟩
  -- ⟨σ₁, γ₁(b₁)⟩ ⭢* ⟨σ₃, bv₁⟩
  -- (σ₂, σ₃) : 𝓦₁
  -- (𝓦₁, bv₀, bv₁) ∈ 𝓥⟦τ𝕒⟧
  simp only [log_equiv_expr] at Hb
  have ⟨𝓦₁, σ₂, σ₃, bv₀, bv₁, Hfuture₀, HstepBind₀, HstepBind₁, Hsem_store, Hsem_value_bind⟩ := Hb _ _ _ HsemΓ _ _ Hsem_store
  have ⟨HwfBind₀, HwfBind₁⟩ := log_equiv_value.syntactic.wf _ _ _ _ Hsem_value_bind
  have ⟨HvalueBind₀, HvalueBind₁⟩ := log_equiv_value.syntactic.value _ _ _ _ Hsem_value_bind
  --
  --
  -- (𝓦₁, (x ↦ bv₀, γ₀)(e₀), (x ↦ bv₁, γ₁)(e₁)) ∈ 𝓔⟦τ𝕓⟧
  -- ———————————————————————————————————————————————————
  -- 𝓦₂ ⊒ 𝓦₁
  -- ⟨σ₂, (x ↦ bv₀, γ₀)(e₀)⟩ ⭢* ⟨σ₄, v₀⟩
  -- ⟨σ₃, (x ↦ bv₁, γ₁)(e₁)⟩ ⭢* ⟨σ₅, v₁⟩
  -- (σ₄, σ₅) : 𝓦₂
  -- (𝓦₂, v₀, v₁) ∈ 𝓥⟦τ𝕓⟧
  have HsemΓ := log_equiv_env.cons _ _ _ _ _ _ _ Hsem_value_bind (log_equiv_env.antimono _ _ _ _ _ HsemΓ Hfuture₀)
  simp only [log_equiv_expr] at He
  have ⟨𝓦₂, σ₄, σ₅, v₀, v₁, Hfuture₁, Hstep₀, Hstep₁, Hsem_store, Hsem_value⟩ := He _ _ _ HsemΓ _ _ Hsem_store
  exists 𝓦₂, σ₄, σ₅, v₀, v₁
  constructor
  . apply World.future.trans _ _ _ Hfuture₁
    apply Hfuture₀
  constructor
  --
  --
  -- ⟨σ₀, γ₀(b₀)⟩ ⭢* ⟨σ₂, bv₀⟩
  -- ⟨σ₂, (x ↦ bv₀, γ₀)(e₀)⟩ ⭢* ⟨σ₄, v₀⟩
  -- ————————————————————————————————————————————
  -- ⟨σ₀, lets x = γ₀(b₀) in γ₀(e₀)⟩ ⭢* ⟨σ₄, v₀⟩
  . simp
    -- left
    apply stepn.trans
    apply stepn_grounded.congruence_under_ctx𝔹 _ _ _ _ _ (ctx𝔹.lets _ _) _ HstepBind₀
    . apply lc.under_msubst _ _ _ Hmwf₀
      rw [← lc.under_opening]
      apply typing.regular _ _ _ _ _ Hτe₀
    . apply grounded.under_msubst _ _ HmG₀ (typing.dynamic_impl_grounded _ _ _ _ Hτb₀)
    -- head
    have HEqSubst₀ : opening 0 bv₀ (msubst γ₀ e₀) = msubst (bv₀ :: γ₀) ({0 ↦ Γ.length} e₀) :=
      by
      rw [msubst, ← comm.msubst_subst _ _ _ _ (by omega) _ Hmwf₀]
      rw [comm.msubst_opening _ _ _ _ (by omega) Hmwf₀]
      rw [HEq₀, intro.subst]
      apply closed.inc; apply closed.under_msubst _ _ Hmwf₀; simp [HEq₀, Hclosed₀]; omega
      apply HwfBind₀.right
    rw [← HEqSubst₀] at Hstep₀
    apply stepn.multi _ _ _ _ Hstep₀
    apply step_lvl.pure _ _ _ _ ctx𝕄.hole
    . constructor
      . apply HwfBind₀.left
      . apply lc.under_msubst _ _ _ Hmwf₀
        rw [← lc.under_opening]
        apply typing.regular _ _ _ _ _ Hτe₀
    . apply head_pure.lets; apply HvalueBind₀
  constructor
  --
  --
  -- ⟨σ₁, γ₁(b₁)⟩ ⭢* ⟨σ₃, bv₁⟩
  -- ⟨σ₃, (x ↦ bv₁, γ₁)(e₁)⟩ ⭢* ⟨σ₅, v₁⟩
  -- ————————————————————————————————————————————
  -- ⟨σ₁, lets x = γ₁(b₁) in γ₁(e₁)⟩ ⭢* ⟨σ₅, v₁⟩
  . simp
    -- left
    apply stepn.trans
    apply stepn_grounded.congruence_under_ctx𝔹 _ _ _ _ _ (ctx𝔹.lets _ _) _ HstepBind₁
    . apply lc.under_msubst _ _ _ Hmwf₁
      rw [← lc.under_opening]
      apply typing.regular _ _ _ _ _ Hτe₁
    . apply grounded.under_msubst _ _ HmG₁ (typing.dynamic_impl_grounded _ _ _ _ Hτb₁)
    -- head
    have HEqSubst₁ : opening 0 bv₁ (msubst γ₁ e₁) = msubst (bv₁ :: γ₁) ({0 ↦ Γ.length} e₁) :=
      by
      rw [msubst, ← comm.msubst_subst _ _ _ _ (by omega) _ Hmwf₁]
      rw [comm.msubst_opening _ _ _ _ (by omega) Hmwf₁]
      rw [HEq₁, intro.subst]
      apply closed.inc; apply closed.under_msubst _ _ Hmwf₁; simp [HEq₁, Hclosed₁]; omega
      apply HwfBind₁.right
    rw [← HEqSubst₁] at Hstep₁
    apply stepn.multi _ _ _ _ Hstep₁
    apply step_lvl.pure _ _ _ _ ctx𝕄.hole
    . constructor
      . apply HwfBind₁.left
      . apply lc.under_msubst _ _ _ Hmwf₁
        rw [← lc.under_opening]
        apply typing.regular _ _ _ _ _ Hτe₁
    . apply head_pure.lets; apply HvalueBind₁
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
  intros Γ n₀ n₁ Hn
  have ⟨HτNat₀, HτNat₁, Hn⟩ := Hn
  have Hτ₀ : typing Γ 𝟚 (.alloc₁ n₀) (.ref .nat) ⊥ :=
    by
    apply typing.alloc₁; apply HτNat₀
  have Hτ₁ : typing Γ 𝟚 (.alloc₁ n₁) (.ref .nat) ⊥ :=
    by
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
  -- ——————————————————————————
  -- 𝓦₁ ⊒ 𝓦₀
  -- ⟨σ₀, γ₀(n₀)⟩ ⭢* ⟨σ₂, nv₀⟩
  -- ⟨σ₁, γ₁(n₁)⟩ ⭢* ⟨σ₃, nv₁⟩
  -- (σ₂, σ₃) : 𝓦₁
  -- nv₀ = nv₁
  simp only [log_equiv_expr] at Hn
  have ⟨𝓦₁, σ₂, σ₃, nv₀, nv₁, Hfuture₀, HstepNat₀, HstepNat₁, Hsem_store, Hsem_value_nat⟩ := Hn _ _ _ HsemΓ _ _ Hsem_store
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
  -- ⟨σ₀, γ₀(n₀)⟩ ⭢* ⟨σ₂, nv₀⟩
  -- —————————————————————————————————————————————————
  -- ⟨σ₀, alloc γ₀(n₀)⟩ ⭢* ⟨nv₀ :: σ₂, loc σ₂.length⟩
  . simp
    -- left
    apply stepn.trans
    apply stepn_grounded.congruence_under_ctx𝔹 _ _ _ _ _ ctx𝔹.alloc₁ _ HstepNat₀
    . apply grounded.under_msubst _ _ HmG₀ (typing.dynamic_impl_grounded _ _ _ _ HτNat₀)
    -- head
    apply stepn.multi _ _ _ _ (stepn.refl _)
    apply step_lvl.mutable _ _ _ _ _ ctx𝕄.hole
    . simp
    . apply head_mutable.alloc₁
  constructor
  --
  --
  -- ⟨σ₁, γ₁(n₁)⟩ ⭢* ⟨σ₃, nv₁⟩
  -- —————————————————————————————————————————————————
  -- ⟨σ₁, alloc γ₁(n₁)⟩ ⭢* ⟨nv₁ :: σ₃, loc σ₃.length⟩
  . simp
    -- left
    apply stepn.trans
    apply stepn_grounded.congruence_under_ctx𝔹 _ _ _ _ _ ctx𝔹.alloc₁ _ HstepNat₁
    . apply grounded.under_msubst _ _ HmG₁ (typing.dynamic_impl_grounded _ _ _ _ HτNat₁)
    -- head
    apply stepn.multi _ _ _ _ (stepn.refl _)
    apply step_lvl.mutable _ _ _ _ _ ctx𝕄.hole
    . simp
    . apply head_mutable.alloc₁
  constructor
  . rw [Hsem_value_nat]
    apply log_well_store.alloc _ _ _ _ Hsem_store
  . simp

-- Γ ⊧ l₀ ≈𝑙𝑜𝑔 l₁ : ref ℕ
-- ————————————————————————
-- Γ ⊧ !l₀ ≈𝑙𝑜𝑔 !l₁ : ref ℕ
lemma compatibility.load₁ :
  ∀ Γ l₀ l₁,
    log_equiv Γ l₀ l₁ (.ref .nat) →
    log_equiv Γ (.load₁ l₀) (.load₁ l₁) .nat :=
  by
  intros Γ l₀ l₁ Hl
  have ⟨HτLoc₀, HτLoc₁, Hl⟩ := Hl
  have Hτ₀ : typing Γ 𝟚 (.load₁ l₀) .nat ⊥ :=
    by
    apply typing.load₁; apply HτLoc₀
  have Hτ₁ : typing Γ 𝟚 (.load₁ l₁) .nat ⊥ :=
    by
    apply typing.load₁; apply HτLoc₁
  constructor; apply Hτ₀
  constructor; apply Hτ₁
  intros 𝓦₀ γ₀ γ₁ HsemΓ
  have ⟨HmG₀, HmG₁⟩ := log_equiv_env.syntactic.mgrounded _ _ _ _ HsemΓ
  simp only [log_equiv_expr]
  intros σ₀ σ₁ Hsem_store
  --
  --
  -- Γ ⊧ l₀ ≈𝑙𝑜𝑔 l₁ : ref ℕ
  -- ——————————————————————————
  -- 𝓦₁ ⊒ 𝓦₀
  -- ⟨σ₀, γ₀(l₀)⟩ ⭢* ⟨σ₂, lv₀⟩
  -- ⟨σ₁, γ₁(l₁)⟩ ⭢* ⟨σ₃, lv₁⟩
  -- (σ₂, σ₃) : 𝓦₁
  -- 𝓦₁ lv₀ lv₁
  simp only [log_equiv_expr] at Hl
  have ⟨𝓦₁, σ₂, σ₃, lv₀, lv₁, Hfuture₀, HstepLoc₀, HstepLoc₁, Hsem_store, Hsem_value_loc⟩ := Hl _ _ _ HsemΓ _ _ Hsem_store
  have ⟨HvalueLoc₀, HvalueLoc₁⟩ := log_equiv_value.syntactic.value _ _ _ _ Hsem_value_loc
  cases HvalueLoc₀ <;> try simp at Hsem_value_loc
  case loc lv₀ =>
  cases HvalueLoc₁ <;> try simp at Hsem_value_loc
  case loc lv₁ =>
  have ⟨n, Hbinds₀, Hbinds₁⟩ := Hsem_store.right _ _ Hsem_value_loc
  exists 𝓦₁, σ₂, σ₃, .lit n, .lit n
  constructor
  . apply Hfuture₀
  constructor
  --
  --
  -- ⟨σ₀, γ₀(l₀)⟩ ⭢* ⟨σ₂, lv₀⟩
  -- ———————————————————————————————
  -- ⟨σ₀, !γ₀(l₀)⟩ ⭢* ⟨σ₂, σ₂(lv₀)⟩
  . simp
    -- left
    apply stepn.trans
    apply stepn_grounded.congruence_under_ctx𝔹 _ _ _ _ _ ctx𝔹.load₁ _ HstepLoc₀
    . apply grounded.under_msubst _ _ HmG₀ (typing.dynamic_impl_grounded _ _ _ _ HτLoc₀)
    -- head
    apply stepn.multi _ _ _ _ (stepn.refl _)
    apply step_lvl.mutable _ _ _ _ _ ctx𝕄.hole
    . simp
    . apply head_mutable.load₁; apply Hbinds₀
  constructor
  --
  --
  -- ⟨σ₁, γ₁(l₁)⟩ ⭢* ⟨σ₃, lv₁⟩
  -- ———————————————————————————————
  -- ⟨σ₁, !γ₁(l₁)⟩ ⭢* ⟨σ₃, σ₃(lv₁)⟩
  . simp
    -- left
    apply stepn.trans
    apply stepn_grounded.congruence_under_ctx𝔹 _ _ _ _ _ ctx𝔹.load₁ _ HstepLoc₁
    . apply grounded.under_msubst _ _ HmG₁ (typing.dynamic_impl_grounded _ _ _ _ HτLoc₁)
    -- head
    apply stepn.multi _ _ _ _ (stepn.refl _)
    apply step_lvl.mutable _ _ _ _ _ ctx𝕄.hole
    . simp
    . apply head_mutable.load₁; apply Hbinds₁
  constructor
  . apply Hsem_store
  . simp

-- Γ ⊧ l₀ ≈𝑙𝑜𝑔 l₁ : ref ℕ
-- Γ ⊧ n₀ ≈𝑙𝑜𝑔 n₁ : ℕ
-- —————————————————————————————————————
-- Γ ⊧ (l₀ := n₀) ≈𝑙𝑜𝑔 (l₁ := n₁) : unit
lemma compatibility.store₁ :
  ∀ Γ l₀ l₁ n₀ n₁,
    log_equiv Γ l₀ l₁ (.ref .nat) →
    log_equiv Γ n₀ n₁ .nat →
    log_equiv Γ (.store₁ l₀ n₀) (.store₁ l₁ n₁) .unit :=
  by
  intros Γ l₀ l₁ n₀ n₁ Hl Hn
  have ⟨HτLoc₀, HτLoc₁, Hl⟩ := Hl
  have ⟨HτNat₀, HτNat₁, Hn⟩ := Hn
  have Hτ₀ : typing Γ 𝟚 (.store₁ l₀ n₀) .unit ⊥ :=
    by
    rw [← Effect.union_pure ⊥]
    apply typing.store₁; apply HτLoc₀; apply HτNat₀
  have Hτ₁ : typing Γ 𝟚 (.store₁ l₁ n₁) .unit ⊥ :=
    by
    rw [← Effect.union_pure ⊥]
    apply typing.store₁; apply HτLoc₁; apply HτNat₁
  constructor; apply Hτ₀
  constructor; apply Hτ₁
  intros 𝓦₀ γ₀ γ₁ HsemΓ
  have ⟨Hmwf₀, Hmwf₁⟩ := log_equiv_env.syntactic.mwf _ _ _ _ HsemΓ
  have ⟨HmG₀, HmG₁⟩ := log_equiv_env.syntactic.mgrounded _ _ _ _ HsemΓ
  simp only [log_equiv_expr]
  intros σ₀ σ₁ Hsem_store
  --
  --
  -- Γ ⊧ l₀ ≈𝑙𝑜𝑔 l₁ : ℕ
  -- ——————————————————————————
  -- 𝓦₁ ⊒ 𝓦₀
  -- ⟨σ₀, γ₀(l₀)⟩ ⭢* ⟨σ₂, lv₀⟩
  -- ⟨σ₁, γ₁(l₁)⟩ ⭢* ⟨σ₃, lv₁⟩
  -- (σ₂, σ₃) : 𝓦₁
  -- 𝓦₁ lv₀ lv₁
  simp only [log_equiv_expr] at Hl
  have ⟨𝓦₁, σ₂, σ₃, lv₀, lv₁, Hfuture₀, HstepLoc₀, HstepLoc₁, Hsem_store, Hsem_value_loc⟩ := Hl _ _ _ HsemΓ _ _ Hsem_store
  have ⟨HvalueLoc₀, HvalueLoc₁⟩ := log_equiv_value.syntactic.value _ _ _ _ Hsem_value_loc
  cases HvalueLoc₀ <;> try simp at Hsem_value_loc
  case loc lv₀ =>
  cases HvalueLoc₁ <;> try simp at Hsem_value_loc
  case loc lv₁ =>
  --
  --
  -- Γ ⊧ n₀ ≈𝑙𝑜𝑔 n₁ : ℕ
  -- ——————————————————————————
  -- 𝓦₂ ⊒ 𝓦₁
  -- ⟨σ₂, γ₀(n₀)⟩ ⭢* ⟨σ₄, nv₀⟩
  -- ⟨σ₃, γ₁(n₁)⟩ ⭢* ⟨σ₅, nv₁⟩
  -- (σ₄, σ₅) : 𝓦₂
  -- nv₀ = nv₁
  simp only [log_equiv_expr] at Hn
  have ⟨𝓦₂, σ₄, σ₅, nv₀, nv₁, Hfuture₁, HstepNat₀, HstepNat₁, Hsem_store, Hsem_value_nat⟩ := Hn _ _ _ (log_equiv_env.antimono _ _ _ _ _ HsemΓ Hfuture₀) _ _ Hsem_store
  have ⟨HvalueNat₀, HvalueNat₁⟩ := log_equiv_value.syntactic.value _ _ _ _ Hsem_value_nat
  cases HvalueNat₀ <;> try simp at Hsem_value_nat
  case lit nv₀ =>
  cases HvalueNat₁ <;> try simp at Hsem_value_nat
  case lit nv₁ =>
  have Hsem_value_loc := Hfuture₁ _ _ Hsem_value_loc
  have ⟨n, Hbinds₀, Hbinds₁⟩ := Hsem_store.right _ _ Hsem_value_loc
  have ⟨σ₆, Hpatch₀⟩ : ∃ σ₆, patch lv₀ (.lit nv₀) σ₄ σ₆ :=
    by
    simp [← setr_exists_iff_index_lt_length, getr_exists_iff_index_lt_length]
    exists .lit n
  have ⟨σ₇, Hpatch₁⟩ : ∃ σ₇, patch lv₁ (.lit nv₁) σ₅ σ₇ :=
    by
    simp [← setr_exists_iff_index_lt_length, getr_exists_iff_index_lt_length]
    exists .lit n
  exists 𝓦₂, σ₆, σ₇, .unit, .unit
  constructor
  . apply World.future.trans _ _ _ Hfuture₁
    apply Hfuture₀
  constructor
  --
  --
  -- ⟨σ₀, γ₀(l₀)⟩ ⭢* ⟨σ₂, lv₀⟩
  -- ⟨σ₂, γ₀(n₀)⟩ ⭢* ⟨σ₄, nv₀⟩
  -- ——————————————————————————————————————————————
  -- ⟨σ₀, γ₀(l₀) := γ₀(n₀)⟩ ⭢* ⟨(lv₀ ↦ nv₀)σ₄, ()⟩
  . simp
    -- left
    apply stepn.trans
    apply stepn_grounded.congruence_under_ctx𝔹 _ _ _ _ _ (ctx𝔹.storel₁ _ _) _ HstepLoc₀
    . apply lc.under_msubst _ _ _ Hmwf₀ (typing.regular _ _ _ _ _ HτNat₀)
    . apply grounded.under_msubst _ _ HmG₀ (typing.dynamic_impl_grounded _ _ _ _ HτLoc₀)
    -- right
    apply stepn.trans
    apply stepn_grounded.congruence_under_ctx𝔹 _ _ _ _ _ (ctx𝔹.storer₁ _ _) _ HstepNat₀
    . apply value.loc
    . apply grounded.under_msubst _ _ HmG₀ (typing.dynamic_impl_grounded _ _ _ _ HτNat₀)
    -- head
    apply stepn.multi _ _ _ _ (stepn.refl _)
    apply step_lvl.mutable _ _ _ _ _ ctx𝕄.hole
    . simp
    . apply head_mutable.store₁; apply Hpatch₀
  constructor
  --
  --
  -- ⟨σ₁, γ₁(l₁)⟩ ⭢* ⟨σ₃, lv₁⟩
  -- ⟨σ₃, γ₁(n₁)⟩ ⭢* ⟨σ₅, nv₁⟩
  -- ——————————————————————————————————————————————
  -- ⟨σ₁, γ₁(l₁) := γ₁(n₁)⟩ ⭢* ⟨(lv₁ ↦ nv₁)σ₅, ()⟩
  . simp
    -- left
    apply stepn.trans
    apply stepn_grounded.congruence_under_ctx𝔹 _ _ _ _ _ (ctx𝔹.storel₁ _ _) _ HstepLoc₁
    . apply lc.under_msubst _ _ _ Hmwf₁ (typing.regular _ _ _ _ _ HτNat₁)
    . apply grounded.under_msubst _ _ HmG₁ (typing.dynamic_impl_grounded _ _ _ _ HτLoc₁)
    -- right
    apply stepn.trans
    apply stepn_grounded.congruence_under_ctx𝔹 _ _ _ _ _ (ctx𝔹.storer₁ _ _) _ HstepNat₁
    . apply value.loc
    . apply grounded.under_msubst _ _ HmG₁ (typing.dynamic_impl_grounded _ _ _ _ HτNat₁)
    -- head
    apply stepn.multi _ _ _ _ (stepn.refl _)
    apply step_lvl.mutable _ _ _ _ _ ctx𝕄.hole
    . simp
    . apply head_mutable.store₁; apply Hpatch₁
  constructor
  . apply log_well_store.store
    . apply Hsem_store
    . apply Hsem_value_loc
    . apply Hpatch₀
    . simp [Hsem_value_nat]
      apply Hpatch₁
  . simp
