import CollapsingTowers.TwoLevelBasic.LogicalEquiv.LogicalRelation

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
  intros γ₀ γ₁ HsemΓ
  simp only [log_equiv_expr]
  exists msubst γ₀ (.fvar x), msubst γ₁ (.fvar x)
  constructor; apply stepn.refl
  constructor; apply stepn.refl
  apply log_equiv_env.binds_log_equiv_value _ _ _ _ _ HsemΓ Hbinds

-- Γ ⊧ n ≈𝑙𝑜𝑔 n : ℕ
lemma compatibility.lit :
  ∀ Γ n,
    log_equiv Γ (.lit n) (.lit n) .nat :=
  by
  intros _ n
  constructor; apply typing.lit
  constructor; apply typing.lit
  intros γ₀ γ₁ HsemΓ
  simp only [log_equiv_expr]
  exists .lit n, .lit n
  constructor; simp; apply stepn.refl
  constructor; simp; apply stepn.refl
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
  intros γ₀ γ₁ HsemΓ
  have ⟨Hmwf₀, Hmwf₁⟩ := log_equiv_env.mwf _ _ _ HsemΓ
  have ⟨HEq₀, HEq₁⟩ := log_equiv_env.length _ _ _ HsemΓ
  have ⟨HSτ₀, HSτ₁⟩ := log_equiv_env.msubst.typing _ _ _ _ _ _ Hτ₀ Hτ₁ HsemΓ
  have ⟨Hlc₀, Hclosed₀⟩ := typing.wf _ _ _ _ _ HSτ₀
  have ⟨Hlc₁, Hclosed₁⟩ := typing.wf _ _ _ _ _ HSτ₁
  simp at HSτ₀ HSτ₁ Hlc₀ Hlc₁ Hclosed₀ Hclosed₁
  simp only [log_equiv_expr]
  exists msubst γ₀ (.lam e₀), msubst γ₁ (.lam e₁)
  constructor; apply stepn.refl
  constructor; apply stepn.refl
  simp only [msubst.lam, log_equiv_value]
  constructor; apply HSτ₀
  constructor; apply HSτ₁
  intros argv₀ argv₁ Hsem_value_arg
  have ⟨HvalueArg₀, HvalueArg₁⟩ := log_equiv_value.syntactic.value _ _ _ Hsem_value_arg
  have ⟨HτArg₀, HτArg₁⟩ := log_equiv_value.syntactic.typing _ _ _ Hsem_value_arg
  have ⟨HlcArg₀, HclosedArg₀⟩ := typing.wf _ _ _ _ _ HτArg₀
  have ⟨HlcArg₁, HclosedArg₁⟩ := typing.wf _ _ _ _ _ HτArg₁
  --
  --
  -- ((x ↦ argv₀, γ₀)(e₀), (x ↦ argv₁, γ₁)(e₁)) ∈ 𝓔⟦τ𝕓⟧
  -- ———————————————————————————————————————————————————
  -- (x ↦ argv₀, γ₀)(e₀) ⇝* v₀
  -- (x ↦ argv₁, γ₁)(e₁) ⇝* v₁
  -- (v₀, v₁) ∈ 𝓥⟦τ𝕓⟧
  have HsemΓ := log_equiv_env.cons _ _ _ _ _ _ Hsem_value_arg HsemΓ
  simp only [log_equiv_expr] at He
  have ⟨v₀, v₁, Hstep₀, Hstep₁, Hsem_value⟩ := He _ _ HsemΓ
  simp only [log_equiv_expr]
  exists v₀, v₁
  constructor
  -- (x ↦ argv₀, γ₀)(e₀) ⇝* v₀
  -- ——————————————————————————
  -- λx.e₀ @ argv₀ ⇝* v₀
  . have HEqSubst₀ : opening 0 argv₀ (msubst γ₀ e₀) = msubst (argv₀ :: γ₀) ({0 ↦ Γ.length} e₀) :=
      by
      rw [msubst, ← comm.msubst_subst _ _ _ _ _ _ Hmwf₀]
      rw [comm.msubst_opening _ _ _ _ _ Hmwf₀]
      rw [HEq₀, intro.subst]
      apply closed.inc; apply Hclosed₀; simp
      omega; omega; apply HclosedArg₀
    rw [← HEqSubst₀] at Hstep₀
    apply stepn.multi _ _ _ _ Hstep₀
    apply step_lvl.pure _ _ _ ctx𝕄.hole
    constructor; apply Hlc₀; apply lc.value; apply HvalueArg₀
    apply head.app₁; apply HvalueArg₀
  constructor
  -- (x ↦ argv₁, γ₁)(e₁) ⇝* v₁
  -- ——————————————————————————
  -- λx.e₁ @ argv₁ ⇝* v₁
  . have HEqSubst₁ : opening 0 argv₁ (msubst γ₁ e₁) = msubst (argv₁ :: γ₁) ({0 ↦ Γ.length} e₁) :=
      by
      rw [msubst, ← comm.msubst_subst _ _ _ _ _ _ Hmwf₁]
      rw [comm.msubst_opening _ _ _ _ _ Hmwf₁]
      rw [HEq₁, intro.subst]
      apply closed.inc; apply Hclosed₁; simp
      omega; omega; apply HclosedArg₁
    rw [← HEqSubst₁] at Hstep₁
    apply stepn.multi _ _ _ _ Hstep₁
    apply step_lvl.pure _ _ _ ctx𝕄.hole
    constructor; apply Hlc₁; apply lc.value; apply HvalueArg₁
    apply head.app₁; apply HvalueArg₁
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
  intros γ₀ γ₁ HsemΓ
  have ⟨HSτFun₀, HSτFun₁⟩ := log_equiv_env.msubst.typing _ _ _ _ _ _ HτFun₀ HτFun₁ HsemΓ
  have ⟨HSτArg₀, HSτArg₁⟩ := log_equiv_env.msubst.typing _ _ _ _ _ _ HτArg₀ HτArg₁ HsemΓ
  --
  --
  -- Γ ⊧ f₀ ≈𝑙𝑜𝑔 f₁ : τ𝕒 → τ𝕓
  -- ————————————————————————
  -- γ₀(f₀) ⇝* fv₀
  -- γ₁(f₁) ⇝* fv₁
  -- (fv₀, fv₁) ∈ 𝓥⟦τ𝕒 → τ𝕓⟧
  simp only [log_equiv_expr] at Hf
  have ⟨fv₀, fv₁, HstepFun₀, HstepFun₁, Hsem_value_fun⟩ := Hf _ _ HsemΓ
  have ⟨HvalueFun₀, HvalueFun₁⟩ := log_equiv_value.syntactic.value _ _ _ Hsem_value_fun
  --
  --
  -- Γ ⊧ arg₀ ≈𝑙𝑜𝑔 arg₁ : τ𝕒
  -- ———————————————————————
  -- γ₀(arg₀) ⇝* argv₀
  -- γ₁(arg₁) ⇝* argv₁
  -- (argv₀, argv₁) ∈ 𝓥⟦τ𝕒⟧
  simp only [log_equiv_expr] at Harg
  have ⟨argv₀, argv₁, HstepArg₀, HstepArg₁, Hsem_value_arg⟩ := Harg _ _ HsemΓ
  --
  --
  -- (fv₀, fv₁) ∈ 𝓥⟦τ𝕒 → τ𝕓⟧
  -- (argv₀, argv₁) ∈ 𝓥⟦τ𝕒⟧
  -- ——————————————————————————————————
  -- (fv₀ @ argv₀, fv₁ @ argv₁) ∈ 𝓔⟦τ𝕓⟧
  have Hsem_expr := log_equiv_value.apply _ _ _ _ _ _ Hsem_value_fun Hsem_value_arg
  --
  --
  -- (fv₀ @ argv₀, fv₁ @ argv₁) ∈ 𝓔⟦τ𝕓⟧
  -- ——————————————————————————————————
  -- fv₀ @ argv₀ ⇝* v₀
  -- fv₁ @ argv₁ ⇝* v₁
  -- (v₀, v₁) ∈ 𝓥⟦τ𝕓⟧
  simp only [log_equiv_expr] at Hsem_expr
  have ⟨v₀, v₁, Hstep₀, Hstep₁, Hsem_value⟩ := Hsem_expr
  simp only [log_equiv_expr]
  exists v₀, v₁
  constructor
  --
  --
  -- γ₀(f₀) ⇝* fv₀
  -- γ₀(arg₀) ⇝* argv₀
  -- fv₀ @ argv₀ ⇝* v₀
  -- ————————————————————————
  -- γ₀(f₀) @ γ₀(arg₀) ⇝* v₀
  . simp
    -- left
    apply stepn.trans
    apply stepn_grounded.congruence_under_ctx𝔹 _ _ _ (ctx𝔹.appl₁ _ _)
    apply typing.dynamic_impl_grounded _ _ _ _ HSτFun₀; apply HstepFun₀
    apply typing.regular _ _ _ _ _ HSτArg₀
    -- right
    apply stepn.trans
    apply stepn_grounded.congruence_under_ctx𝔹 _ _ _ (ctx𝔹.appr₁ _ HvalueFun₀)
    apply typing.dynamic_impl_grounded _ _ _ _ HSτArg₀; apply HstepArg₀
    -- head
    apply Hstep₀
  constructor
  --
  --
  -- γ₁(f₁) ⇝* fv₁
  -- γ₁(arg₁) ⇝* argv₁
  -- fv₁ @ argv₁ ⇝* v₁
  -- ————————————————————————
  -- γ₁(f₁) @ γ₁(arg₁) ⇝* v₁
  . simp
    -- left
    apply stepn.trans
    apply stepn_grounded.congruence_under_ctx𝔹 _ _ _ (ctx𝔹.appl₁ _ _)
    apply typing.dynamic_impl_grounded _ _ _ _ HSτFun₁; apply HstepFun₁
    apply typing.regular _ _ _ _ _ HSτArg₁
    -- right
    apply stepn.trans
    apply stepn_grounded.congruence_under_ctx𝔹 _ _ _ (ctx𝔹.appr₁ _ HvalueFun₁)
    apply typing.dynamic_impl_grounded _ _ _ _ HSτArg₁; apply HstepArg₁
    -- head
    apply Hstep₁
  . apply Hsem_value
