import CollapsingTowers.TwoLevelFinal.LogicalEquiv.LogicalRelation

-- Γ ⊧ x ≤𝑙𝑜𝑔 x : Γ(x)
lemma compatibility.fvar :
  ∀ Γ x τ,
    binds x (τ, 𝟚) Γ →
    wbt 𝟚 τ →
    log_approx Γ (.fvar x) (.fvar x) τ :=
  by
  intros Γ x τ Hbinds Hwbt
  constructor; apply typing.fvar; apply Hbinds; apply Hwbt
  constructor; apply typing.fvar; apply Hbinds; apply Hwbt
  intros k 𝓦 γ₀ γ₁ HsemΓ
  simp only [log_approx_expr]
  intros z Hindexz σ₀ σ₁ Hsem_store σ₂ v₀ Hvalue₀ Hstep₀
  have Hsem_value := log_approx_env.binds_log_approx_value _ _ _ _ _ _ _ HsemΓ Hbinds
  have ⟨Hvalue₀, Hvalue₁⟩ := log_approx_value.syntactic.value _ _ _ _ _ Hsem_value
  have ⟨HEqσ, HEqv, Hz⟩ := stepn_indexed.value_impl_termination _ _ _ _ _ Hvalue₀ Hstep₀
  exists 𝓦, σ₁, msubst γ₁ (.fvar x)
  constructor; simp
  constructor; apply stepn.refl
  constructor; rw [← HEqσ]; apply Hsem_store
  rw [← HEqv, Hz]; apply Hsem_value

-- Γ ⊧ n ≤𝑙𝑜𝑔 n : ℕ
lemma compatibility.lit :
  ∀ Γ n,
    log_approx Γ (.lit n) (.lit n) .nat :=
  by
  intros _ n
  constructor; apply typing.lit
  constructor; apply typing.lit
  intros k 𝓦 γ₀ γ₁ HsemΓ
  simp only [log_approx_expr]
  intros z Hindexz σ₀ σ₁ Hsem_store σ₂ v₀ Hvalue₀ Hstep₀
  simp at Hstep₀
  have ⟨HEqσ, HEqv, Hz⟩ := stepn_indexed.value_impl_termination _ _ _ _ _ (value.lit n) Hstep₀
  exists 𝓦, σ₁, .lit n
  constructor; simp
  constructor; simp; apply stepn.refl
  constructor; rw [← HEqσ]; apply Hsem_store
  simp [← HEqv, Hz]

-- Γ ⊧ () ≤𝑙𝑜𝑔 () : unit
lemma compatibility.unit :
  ∀ Γ,
    log_approx Γ .unit .unit .unit :=
  by
  intros
  constructor; apply typing.unit
  constructor; apply typing.unit
  intros k 𝓦 γ₀ γ₁ HsemΓ
  simp only [log_approx_expr]
  intros z Hindexz σ₀ σ₁ Hsem_store σ₂ v₀ Hvalue₀ Hstep₀
  simp at Hstep₀
  have ⟨HEqσ, HEqv, Hz⟩ := stepn_indexed.value_impl_termination _ _ _ _ _ value.unit Hstep₀
  exists 𝓦, σ₁, .unit
  constructor; simp
  constructor; simp; apply stepn.refl
  constructor; rw [← HEqσ]; apply Hsem_store
  simp [← HEqv, Hz]

-- x ↦ τ𝕒, Γ ⊧ e₀ ≤𝑙𝑜𝑔 e₁ : τ𝕓
-- ——————————————————————————————
-- Γ ⊧ λx.e₀ ≤𝑙𝑜𝑔 λx.e₁ : τ𝕒 → τ𝕓
lemma compatibility.lam :
  ∀ Γ e₀ e₁ τ𝕒 τ𝕓,
    wbt 𝟚 τ𝕒 →
    closed_at e₀ Γ.length →
    closed_at e₁ Γ.length →
    log_approx ((τ𝕒, 𝟚) :: Γ) ({0 ↦ Γ.length} e₀) ({0 ↦ Γ.length} e₁) τ𝕓 →
    log_approx Γ (.lam e₀) (.lam e₁) (.arrow τ𝕒 τ𝕓 ⊥) :=
  by
  intros Γ e₀ e₁ τ𝕒 τ𝕓 Hwbt Hclosed₀ Hclosed₁ He
  have ⟨Hτ₀, Hτ₁, He⟩ := He
  have Hτ₀ : typing Γ 𝟚 (.lam e₀) (.arrow τ𝕒 τ𝕓 ⊥) ⊥ := by apply typing.lam; apply Hτ₀; apply Hwbt; apply Hclosed₀
  have Hτ₁ : typing Γ 𝟚 (.lam e₁) (.arrow τ𝕒 τ𝕓 ⊥) ⊥ := by apply typing.lam; apply Hτ₁; apply Hwbt; apply Hclosed₁
  constructor; apply Hτ₀
  constructor; apply Hτ₁
  intros k 𝓦₀ γ₀ γ₁ HsemΓ
  have ⟨HEq₀, HEq₁⟩ := log_approx_env.length _ _ _ _ _ HsemΓ
  have ⟨Hmwf₀, Hmwf₁⟩ := log_approx_env.syntactic.mwf _ _ _ _ _ HsemΓ
  have ⟨HmG₀, HmG₁⟩ := log_approx_env.syntactic.mgrounded _ _ _ _ _ HsemΓ
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
  simp only [log_approx_expr]
  intros z Hindexz σ₀ σ₁ Hsem_store σ₂ v₀ Hvalue₀ Hstep₀
  --
  --
  -- ⟨σ₀, λx.γ₀(e₀)⟩ ⇝ ⟦z⟧ ⟨σ₂, v₀⟩
  -- ——————————————————————————————
  -- z = 0
  -- σ₂ = σ₀
  -- v₀ = λx.γ₀(e₀)
  simp at Hstep₀
  have ⟨HEqσ₀, HEqv₀, HEqz⟩ := stepn_indexed.value_impl_termination _ _ _ _ _ (value.lam _ Hwfe₀.left) Hstep₀
  exists 𝓦₀, σ₁, msubst γ₁ (.lam e₁)
  constructor; simp
  constructor; apply stepn.refl
  constructor; rw [← HEqσ₀]; apply Hsem_store
  simp only [← HEqv₀, HEqz, msubst.lam, log_approx_value]
  constructor; apply Hwfe₀
  constructor; apply HG₀
  constructor; apply Hwfe₁
  constructor; apply HG₁
  intros k 𝓦₁ argv₀ argv₁ Hfuture₀ Hsem_value_arg
  have ⟨Hindexk, Hfuture₀⟩ := Hfuture₀
  have ⟨HwfArg₀, HwfArg₁⟩ := log_approx_value.syntactic.wf _ _ _ _ _ Hsem_value_arg
  have ⟨HvalueArg₀, HvalueArg₁⟩ := log_approx_value.syntactic.value _ _ _ _ _ Hsem_value_arg
  simp only [log_approx_expr]
  intros j Hindexj σ₂ σ₃ Hsem_store σ₄ v₀ Hvalue₀ Hstep₀
  --
  --
  -- ⟨σ₂, λx.γ₀(e₀) @ argv₀⟩ ⇝ ⟦j⟧ ⟨σ₄, v₀⟩
  -- —————————————————————————————————————————
  -- j = i + 1
  -- ⟨σ₂, (x ↦ argv₀, γ₀)(e₀)⟩ ⇝ ⟦i⟧ ⟨σ₄, v₀⟩
  have ⟨i, HEqj, Hstep₀⟩ := stepn_indexed.refine.app₁.eliminator _ _ _ _ _ _ (value.lam _ Hwfe₀.left) HvalueArg₀ Hvalue₀ Hstep₀
  --
  --
  -- ⟨σ₂, (x ↦ argv₀, γ₀)(e₀)⟩ ⇝ ⟦i⟧ ⟨σ₄, v₀⟩
  -- (k, 𝓦₁, (x ↦ argv₀, γ₀)(e₀), (x ↦ argv₁, γ₁)(e₁)) ∈ 𝓔⟦τ𝕓⟧
  -- ——————————————————————————————————————————————————————————
  -- ⟨σ₃, (x ↦ argv₁, γ₁)(e₁)⟩ ⇝* ⟨σ₅, v₁⟩
  -- (σ₄, σ₅) : 𝓦₂
  -- (k - i, 𝓦₂, v₀, v₁) ∈ 𝓥⟦τ𝕓⟧
  have HEqSubst₀ : opening 0 argv₀ (msubst γ₀ e₀) = msubst (argv₀ :: γ₀) ({0 ↦ Γ.length} e₀) :=
    by
    rw [msubst, ← comm.msubst_subst _ _ _ _ (by omega) _ Hmwf₀]
    rw [comm.msubst_opening _ _ _ _ (by omega) Hmwf₀]
    rw [HEq₀, intro.subst]
    apply closed.inc; apply Hwfe₀.right; omega
    apply HwfArg₀.right
  rw [HEqSubst₀] at Hstep₀
  have HsemΓ : log_approx_env (k, 𝓦₁) (argv₀ :: γ₀) (argv₁ :: γ₁) ((τ𝕒, 𝟚) :: Γ) :=
    by
    apply log_approx_env.cons; apply Hsem_value_arg
    apply log_approx_env.antimono; apply HsemΓ
    constructor; omega; apply Hfuture₀
  simp only [log_approx_expr] at He
  have ⟨𝓦₂, σ₅, v₁, Hfuture₁, Hstep₁, Hsem_store, Hsem_value⟩ := He _ _ _ _ HsemΓ i (by omega) _ _ Hsem_store _ _ Hvalue₀ Hstep₀
  have ⟨_, Hfuture₁⟩ := Hfuture₁
  --
  --
  -- ⟨σ₃, (x ↦ argv₁, γ₁)(e₁)⟩ ⇝* ⟨σ₅, v₁⟩
  -- ——————————————————————————————————————
  -- ⟨σ₃, λx.γ₁(e₁) @ argv₁⟩ ⇝* ⟨σ₅, v₁⟩
  exists 𝓦₂, σ₅, v₁
  constructor
  . constructor; omega; apply Hfuture₁
  constructor
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
  . apply log_approx_value.antimono
    apply Hsem_value; simp; omega

-- Γ ⊧ f₀ ≤𝑙𝑜𝑔 f₁ : τ𝕒 → τ𝕓
-- Γ ⊧ arg₀ ≤𝑙𝑜𝑔 arg₁ : τ𝕒
-- —————————————————————————————————
-- Γ ⊧ f₀ @ arg₀ ≤𝑙𝑜𝑔 f₁ @ arg₁ : τ𝕓
lemma compatibility.app₁ :
  ∀ Γ f₀ f₁ arg₀ arg₁ τ𝕒 τ𝕓,
    log_approx Γ f₀ f₁ (.arrow τ𝕒 τ𝕓 ⊥) →
    log_approx Γ arg₀ arg₁ τ𝕒 →
    log_approx Γ (.app₁ f₀ arg₀) (.app₁ f₁ arg₁) τ𝕓 :=
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
  intros k 𝓦₀ γ₀ γ₁ HsemΓ
  have ⟨Hmwf₀, Hmwf₁⟩ := log_approx_env.syntactic.mwf _ _ _ _ _ HsemΓ
  have ⟨HmG₀, HmG₁⟩ := log_approx_env.syntactic.mgrounded _ _ _ _ _ HsemΓ
  have HG₀ : grounded (msubst γ₀ (.app₁ f₀ arg₀)) :=
    by
    apply grounded.under_msubst _ _ HmG₀
    apply typing.dynamic_impl_grounded _ _ _ _ Hτ₀
  have HG₁ : grounded (msubst γ₁ (.app₁ f₁ arg₁)) :=
    by
    apply grounded.under_msubst _ _ HmG₁
    apply typing.dynamic_impl_grounded _ _ _ _ Hτ₁
  simp at HG₀ HG₁
  simp only [log_approx_expr]
  intros j Hindexj σ₀ σ₁ Hsem_store σ₂ v₀ Hvalue₀ Hstep₀
  --
  --
  -- ⟨σ₀, γ₀(f₀) @ γ₀(arg₀)⟩ ⇝ ⟦j⟧ ⟨σ₂, v₀⟩
  -- ——————————————————————————————————————
  -- i₀ + i₁ + i₂ = j
  -- ⟨σ₀, γ₀(f₀)⟩ ⇝ ⟦i₀⟧ ⟨imσ₀, fv₀⟩
  -- ⟨imσ₀, γ₀(arg₀)⟩ ⇝ ⟦i₁⟧ ⟨imσ₂, argv₀⟩
  -- ⟨imσ₂, fv₀ @ argv₀⟩ ⇝ ⟦i₂⟧ ⟨σ₂, v₀⟩
  simp at Hstep₀
  have ⟨imσ₀, imσ₂, i₀, i₁, i₂, fv₀, argv₀, HEqj, HvalueFun₀, HvalueArg₀, HstepFun₀, HstepArg₀, Hstep₀⟩ :=
    stepn_indexed.refine.app₁.constructor _ _ _ _ _ _ Hvalue₀ HG₀ Hstep₀
  --
  --
  -- ⟨σ₀, γ₀(f₀)⟩ ⇝ ⟦i₀⟧ ⟨imσ₀, fv₀⟩
  -- Γ ⊧ f₀ ≤𝑙𝑜𝑔 f₁ : τ𝕒 → τ𝕓
  -- ————————————————————————————————————
  -- ⟨σ₁, γ₁(f₁)⟩ ⇝* ⟨imσ₁, fv₁⟩
  -- (imσ₀, imσ₁) : 𝓦₂
  -- (k - i₀, 𝓦₁, fv₀, fv₁) ∈ 𝓥⟦τ𝕒 → τ𝕓⟧
  simp only [log_approx_expr] at Hf
  have ⟨𝓦₁, imσ₁, fv₁, Hfuture₀, HstepFun₁, Hsem_store, Hsem_value_fun⟩ := Hf _ _ _ _ HsemΓ i₀ (by omega) _ _ Hsem_store _ _ HvalueFun₀ HstepFun₀
  have ⟨_, Hfuture₀⟩ := Hfuture₀
  have ⟨HvalueFun₀, HvalueFun₁⟩ := log_approx_value.syntactic.value _ _ _ _ _ Hsem_value_fun
  --
  --
  -- ⟨imσ₀, γ₀(arg₀)⟩ ⇝ ⟦i₁⟧ ⟨imσ₂, argv₀⟩
  -- Γ ⊧ arg₀ ≤𝑙𝑜𝑔 arg₁ : τ𝕒
  -- ————————————————————————————————————————
  -- ⟨imσ₁, γ₁(arg₁)⟩ ⇝* ⟨imσ₃, argv₁⟩
  -- (imσ₂, imσ₃) : 𝓦₂
  -- (k - i₀ - i₁, 𝓦₂, argv₀, argv₁) ∈ 𝓥⟦τ𝕒⟧
  have HsemΓ : log_approx_env (k - i₀, 𝓦₁) γ₀ γ₁ Γ :=
    by
    apply log_approx_env.antimono; apply HsemΓ
    constructor; omega; apply Hfuture₀
  simp only [log_approx_expr] at Harg
  have ⟨𝓦₂, imσ₃, argv₁, Hfuture₁, HstepArg₁, Hsem_store, Hsem_value_arg⟩ := Harg (k - i₀) 𝓦₁ _ _ HsemΓ i₁ (by omega) _ _ Hsem_store _ _ HvalueArg₀ HstepArg₀
  have ⟨_, Hfuture₁⟩ := Hfuture₁
  --
  --
  -- (k - i₀, 𝓦₁, fv₀, fv₁) ∈ 𝓥⟦τ𝕒 → τ𝕓⟧
  -- (k - i₀ - i₁, 𝓦₂, argv₀, argv₁) ∈ 𝓥⟦τ𝕒⟧
  -- ————————————————————————————————————————————————————
  -- (k - i₀ - i₁, 𝓦₂, fv₀ @ argv₀, fv₁ @ argv₁) ∈ 𝓔⟦τ𝕓⟧
  have Hsem_value_fun : log_approx_value (k - i₀ - i₁, 𝓦₂) fv₀ fv₁ (τ𝕒.arrow τ𝕓 ⊥) :=
    by
    apply log_approx_value.antimono; apply Hsem_value_fun
    constructor; omega; apply Hfuture₁
  have Hsem_expr := log_approx_value.apply _ _ _ _ _ _ _ _ Hsem_value_fun Hsem_value_arg
  --
  --
  -- (k - i₀ - i₁, 𝓦₂, fv₀ @ argv₀, fv₁ @ argv₁) ∈ 𝓔⟦τ𝕓⟧
  -- ⟨imσ₂, fv₀ @ argv₀⟩ ⇝ ⟦i₂⟧ ⟨σ₂, v₀⟩
  -- ————————————————————————————————————————————————————
  -- ⟨imσ₃, fv₁ @ argv₁⟩ ⇝* ⟨σ₃, v₁⟩
  -- (σ₂, σ₃) : 𝓦₃
  -- (k - i₀ - i₁ - i₂, 𝓦₃, v₀, v₁) ∈ 𝓥⟦τ𝕓⟧
  simp only [log_approx_expr] at Hsem_expr
  have ⟨𝓦₃, σ₃, v₁, Hfuture₂, Hstep₁, Hsem_store, Hsem_value⟩ := Hsem_expr i₂ (by omega) _ _ Hsem_store _ _ Hvalue₀ Hstep₀
  have ⟨_, Hfuture₂⟩ := Hfuture₂
  --
  --
  -- ⟨σ₁, γ₁(f₁)⟩ ⇝* ⟨imσ₁, fv₁⟩
  -- ⟨imσ₁, γ₁(arg₁)⟩ ⇝* ⟨imσ₃, argv₁⟩
  -- ⟨imσ₃, fv₁ @ argv₁⟩ ⇝* ⟨σ₃, v₁⟩
  -- ————————————————————————————————————
  -- ⟨σ₁, γ₁(f₁) @ γ₁(arg₁)⟩ ⇝* ⟨σ₃, v₁⟩
  exists 𝓦₃, σ₃, v₁
  constructor
  . constructor; omega
    apply World.future.trans _ _ _ Hfuture₂
    apply World.future.trans _ _ _ Hfuture₁
    apply Hfuture₀
  constructor
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
  . apply log_approx_value.antimono
    apply Hsem_value; simp; omega

-- Γ ⊧ l₀ ≤𝑙𝑜𝑔 l₁ : ℕ
-- Γ ⊧ r₀ ≤𝑙𝑜𝑔 r₁ : ℕ
-- ——————————————————————————————
-- Γ ⊧ l₀ ⊕ r₀ ≤𝑙𝑜𝑔 l₁ ⊕ r₁ : ℕ
lemma compatibility.binary₁ :
  ∀ Γ op l₀ l₁ r₀ r₁,
    log_approx Γ l₀ l₁ .nat →
    log_approx Γ r₀ r₁ .nat →
    log_approx Γ (.binary₁ op l₀ r₀) (.binary₁ op l₁ r₁) .nat :=
  by
  intros Γ op l₀ l₁ r₀ r₁ Hl Hr
  have ⟨Hτl₀, Hτl₁, Hl⟩ := Hl
  have ⟨Hτr₀, Hτr₁, Hr⟩ := Hr
  have Hτ₀ : typing Γ 𝟚 (.binary₁ op l₀ r₀) .nat ⊥ :=
    by
    rw [← Effect.union_pure ⊥, ← Effect.union_pure (⊥ ∪ ⊥)]
    apply typing.binary₁; apply Hτl₀; apply Hτr₀
  have Hτ₁ : typing Γ 𝟚 (.binary₁ op l₁ r₁) .nat ⊥ :=
    by
    rw [← Effect.union_pure ⊥, ← Effect.union_pure (⊥ ∪ ⊥)]
    apply typing.binary₁; apply Hτl₁; apply Hτr₁
  constructor; apply Hτ₀
  constructor; apply Hτ₁
  intros k 𝓦₀ γ₀ γ₁ HsemΓ
  have ⟨Hmwf₀, Hmwf₁⟩ := log_approx_env.syntactic.mwf _ _ _ _ _ HsemΓ
  have ⟨HmG₀, HmG₁⟩ := log_approx_env.syntactic.mgrounded _ _ _ _ _ HsemΓ
  have HG₀ : grounded (msubst γ₀ (.binary₁ op l₀ r₀)) :=
    by
    apply grounded.under_msubst _ _ HmG₀
    apply typing.dynamic_impl_grounded _ _ _ _ Hτ₀
  have HG₁ : grounded (msubst γ₁ (.binary₁ op l₁ r₁)) :=
    by
    apply grounded.under_msubst _ _ HmG₁
    apply typing.dynamic_impl_grounded _ _ _ _ Hτ₁
  simp at HG₀ HG₁
  simp only [log_approx_expr]
  intros j Hindexj σ₀ σ₁ Hsem_store σ₂ v₀ Hvalue₀ Hstep₀
  --
  --
  -- ⟨σ₀, γ₀(l₀) ⊕ γ₀(r₀)⟩ ⇝ ⟦j⟧ ⟨σ₂, v₀⟩
  -- ——————————————————————————————————————
  -- i₀ + i₁ + i₂ = j
  -- ⟨σ₀, γ₀(l₀)⟩ ⇝ ⟦i₀⟧ ⟨imσ₀, lv₀⟩
  -- ⟨imσ₀, γ₀(r₀)⟩ ⇝ ⟦i₁⟧ ⟨imσ₂, rv₀⟩
  -- ⟨imσ₂, lv₀ ⊕ rv₀⟩ ⇝ ⟦i₂⟧ ⟨σ₂, v₀⟩
  simp at Hstep₀
  have ⟨imσ₀, imσ₂, i₀, i₁, i₂, lv₀, rv₀, HEqj, Hvaluel₀, Hvaluer₀, Hstepl₀, Hstepr₀, Hstep₀⟩ :=
    stepn_indexed.refine.binary₁.constructor _ _ _ _ _ _ _ Hvalue₀ HG₀ Hstep₀
  --
  --
  -- ⟨σ₀, γ₀(l₀)⟩ ⇝ ⟦i₀⟧ ⟨imσ₀, lv₀⟩
  -- Γ ⊧ l₀ ≤𝑙𝑜𝑔 l₁ : ℕ
  -- ————————————————————————————————————
  -- ⟨σ₁, γ₁(l₁)⟩ ⇝* ⟨imσ₁, lv₁⟩
  -- (imσ₀, imσ₁) : 𝓦₁
  -- lv₀ = lv₁
  simp only [log_approx_expr] at Hl
  have ⟨𝓦₁, imσ₁, lv₁, Hfuture₀, Hstepl₁, Hsem_store, Hsem_valuel⟩ := Hl _ _ _ _ HsemΓ i₀ (by omega) _ _ Hsem_store _ _ Hvaluel₀ Hstepl₀
  have ⟨_, Hfuture₀⟩ := Hfuture₀
  have ⟨Hvaluel₀, Hvaluel₁⟩ := log_approx_value.syntactic.value _ _ _ _ _ Hsem_valuel
  cases Hvaluel₀ <;> try simp at Hsem_valuel
  case lit lv₀ =>
  cases Hvaluel₁ <;> try simp at Hsem_valuel
  case lit lv₁ =>
  --
  --
  -- ⟨imσ₀, γ₀(r₀)⟩ ⇝ ⟦i₁⟧ ⟨imσ₂, rv₀⟩
  -- Γ ⊧ r₀ ≤𝑙𝑜𝑔 r₁ : ℕ
  -- ——————————————————————————————————————
  -- ⟨imσ₁, γ₁(r₁)⟩ ⇝* ⟨imσ₃, rv₁⟩
  -- (imσ₂, imσ₃) : 𝓦₂
  -- rv₀ = rv₁
  simp only [log_approx_expr] at Hr
  have HsemΓ : log_approx_env (k - i₀, 𝓦₁) γ₀ γ₁ Γ :=
    by
    apply log_approx_env.antimono; apply HsemΓ
    constructor; omega; apply Hfuture₀
  have ⟨𝓦₂, imσ₃, rv₁, Hfuture₁, Hstepr₁, Hsem_store, Hsem_valuer⟩ := Hr (k - i₀) 𝓦₁ _ _ HsemΓ i₁ (by omega) _ _ Hsem_store _ _ Hvaluer₀ Hstepr₀
  have ⟨_, Hfuture₁⟩ := Hfuture₁
  have ⟨Hvaluer₀, Hvaluer₁⟩ := log_approx_value.syntactic.value _ _ _ _ _ Hsem_valuer
  cases Hvaluer₀ <;> try simp at Hsem_valuer
  case lit rv₀ =>
  cases Hvaluer₁ <;> try simp at Hsem_valuer
  case lit rv₁ =>
  --
  --
  -- ⟨imσ₂, lv₀ ⊕ rv₀⟩ ⇝ ⟦i₂⟧ ⟨σ₂, v₀⟩
  -- ——————————————————————————————————
  -- imσ₂ = imσ₂
  -- v₀ = lv₀ ⊕ rv₀
  have ⟨HEqσ₂, _, HEqv₀⟩ := stepn_indexed.refine.binary₁.eliminator _ _ _ _ _ _ _ Hvalue₀ Hstep₀
  --
  --
  -- ⟨σ₁, γ₁(l₁)⟩ ⇝* ⟨imσ₁, lv₁⟩
  -- ⟨imσ₁, γ₁(r₁)⟩ ⇝* ⟨imσ₃, rv₁⟩
  -- ————————————————————————————————————————————
  -- ⟨σ₁, γ₁(l₁) ⊕ γ₁(r₁)⟩ ⇝* ⟨imσ₃, lv₁ ⊕ rv₁⟩
  exists 𝓦₂, imσ₃, v₀
  constructor
  . constructor; omega
    apply World.future.trans _ _ _ Hfuture₁
    apply Hfuture₀
  constructor
  . simp
    -- left
    apply stepn.trans
    apply stepn_grounded.congruence_under_ctx𝔹 _ _ _ _ _ (ctx𝔹.binaryl₁ _ _ _) _ Hstepl₁
    . apply lc.under_msubst _ _ _ Hmwf₁ (typing.regular _ _ _ _ _ Hτr₁)
    . apply grounded.under_msubst _ _ HmG₁ (typing.dynamic_impl_grounded _ _ _ _ Hτl₁)
    -- right
    apply stepn.trans
    apply stepn_grounded.congruence_under_ctx𝔹 _ _ _ _ _ (ctx𝔹.binaryr₁ _ _ _) _ Hstepr₁
    . apply value.lit
    . apply grounded.under_msubst _ _ HmG₁ (typing.dynamic_impl_grounded _ _ _ _ Hτr₁)
    -- head
    rw [← Hsem_valuel, ← Hsem_valuer, HEqv₀]
    apply stepn.multi _ _ _ _ (stepn.refl _)
    apply step_lvl.pure _ _ _ _ ctx𝕄.hole
    . simp
    . apply head_pure.binary₁
  constructor
  . rw [← HEqσ₂]; apply Hsem_store
  . simp [HEqv₀]

-- Γ ⊧ b₀ ≤𝑙𝑜𝑔 b₁ : τ𝕒
-- x ↦ τ𝕒, Γ ⊧ e₀ ≤𝑙𝑜𝑔 e₁ : τ𝕓
-- —————————————————————————————————————————————————
-- Γ ⊧ lets x = b₀ in e₀ ≤𝑙𝑜𝑔 lets x = b₁ in e₁ : τ𝕓
lemma compatibility.lets :
  ∀ Γ b₀ b₁ e₀ e₁ τ𝕒 τ𝕓,
    wbt 𝟚 τ𝕒 →
    closed_at e₀ Γ.length →
    closed_at e₁ Γ.length →
    log_approx Γ b₀ b₁ τ𝕒 →
    log_approx ((τ𝕒, 𝟚) :: Γ) ({0 ↦ Γ.length} e₀) ({0 ↦ Γ.length} e₁) τ𝕓 →
    log_approx Γ (.lets b₀ e₀) (.lets b₁ e₁) τ𝕓 :=
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
  intros k 𝓦₀ γ₀ γ₁ HsemΓ
  have ⟨HEq₀, HEq₁⟩ := log_approx_env.length _ _ _ _ _ HsemΓ
  have ⟨Hmwf₀, Hmwf₁⟩ := log_approx_env.syntactic.mwf _ _ _ _ _ HsemΓ
  have ⟨HmG₀, HmG₁⟩ := log_approx_env.syntactic.mgrounded _ _ _ _ _ HsemΓ
  have HG₀ : grounded (msubst γ₀ (.lets b₀ e₀)) :=
    by
    apply grounded.under_msubst _ _ HmG₀
    apply typing.dynamic_impl_grounded _ _ _ _ Hτ₀
  have HG₁ : grounded (msubst γ₁ (.lets b₁ e₁)) :=
    by
    apply grounded.under_msubst _ _ HmG₁
    apply typing.dynamic_impl_grounded _ _ _ _ Hτ₁
  simp at HG₀ HG₁
  simp only [log_approx_expr]
  intros j Hindexj σ₀ σ₁ Hsem_store σ₂ v₀ Hvalue₀ Hstep₀
  --
  --
  -- ⟨σ₀, lets x = γ₀(b₀) in γ₀(e₀)⟩ ⇝ ⟦j⟧ ⟨σ₂, v₀⟩
  -- ——————————————————————————————————————————————
  -- i₀ + 1 + i₁ = j
  -- ⟨σ₀, γ₀(b₀)⟩ ⇝ ⟦i₀⟧ ⟨imσ₀, bv₀⟩
  -- ⟨imσ₀, (x ↦ bv₀, γ₀)(e₀)⟩ ⇝ ⟦i₁⟧ ⟨σ₂, v₀⟩
  simp at Hstep₀
  have ⟨imσ₀, i₀, i₁, bv₀, HEqj, HvalueBind₀, HstepBind₀, Hstep₀⟩ :=
    stepn_indexed.refine.lets _ _ _ _ _ _ Hvalue₀ HG₀ Hstep₀
  --
  --
  -- ⟨σ₀, γ₀(b₀)⟩ ⇝ ⟦i₀⟧ ⟨imσ₀, bv₀⟩
  -- Γ ⊧ b₀ ≤𝑙𝑜𝑔 b₁ : τ𝕒
  -- ——————————————————————————————
  -- ⟨σ₁, γ₁(b₁)⟩ ⇝* ⟨imσ₁, bv₁⟩
  -- (imσ₀, imσ₁) : 𝓦₁
  -- (k - i₀, 𝓦₁, bv₀, bv₁) ∈ 𝓥⟦τ𝕒⟧
  simp only [log_approx_expr] at Hb
  have ⟨𝓦₁, imσ₁, bv₁, Hfuture₀, HstepBind₁, Hsem_store, Hsem_value_bind⟩ := Hb _ _ _ _ HsemΓ i₀ (by omega) _ _ Hsem_store _ _ HvalueBind₀ HstepBind₀
  have ⟨_, Hfuture₀⟩ := Hfuture₀
  have ⟨HwfBind₀, HwfBind₁⟩ := log_approx_value.syntactic.wf _ _ _ _ _ Hsem_value_bind
  have ⟨HvalueBind₀, HvalueBind₁⟩ := log_approx_value.syntactic.value _ _ _ _ _ Hsem_value_bind
  --
  --
  -- ⟨imσ₀, (x ↦ bv₀, γ₀)(e₀)⟩ ⇝ ⟦i₁⟧ ⟨σ₂, v₀⟩
  -- (k - i₀, 𝓦₁, (x ↦ bv₀, γ₀)(e₀), (x ↦ bv₁, γ₁)(e₁)) ∈ 𝓔⟦τ𝕓⟧
  -- ———————————————————————————————————————————————————————————
  -- ⟨imσ₁, (x ↦ bv₁, γ₁)(e₁)⟩ ⇝* ⟨σ₃, v₁⟩
  -- (σ₂, σ₃) : 𝓦₂
  -- (k - i₀ - i₁, 𝓦₂, v₀, v₁) ∈ 𝓥⟦τ𝕓⟧
  have HEqSubst₀ : opening 0 bv₀ (msubst γ₀ e₀) = msubst (bv₀ :: γ₀) ({0 ↦ Γ.length} e₀) :=
    by
    rw [msubst, ← comm.msubst_subst _ _ _ _ (by omega) _ Hmwf₀]
    rw [comm.msubst_opening _ _ _ _ (by omega) Hmwf₀]
    rw [HEq₀, intro.subst]
    apply closed.inc; apply closed.under_msubst _ _ Hmwf₀; simp [HEq₀, Hclosed₀]; omega
    apply HwfBind₀.right
  rw [HEqSubst₀] at Hstep₀
  have HsemΓ : log_approx_env (k - i₀, 𝓦₁) (bv₀ :: γ₀) (bv₁ :: γ₁) ((τ𝕒, 𝟚) :: Γ) :=
    by
    apply log_approx_env.cons; apply Hsem_value_bind
    apply log_approx_env.antimono; apply HsemΓ
    constructor; omega; apply Hfuture₀
  have Hsem_expr := He _ _ _ _ HsemΓ
  simp only [log_approx_expr] at Hsem_expr
  have ⟨𝓦₂, σ₃, v₁, Hfuture₁, Hstep₁, Hsem_store, Hsem_value⟩ := Hsem_expr i₁ (by omega) _ _ Hsem_store _ _ Hvalue₀ Hstep₀
  have ⟨_, Hfuture₁⟩ := Hfuture₁
  --
  --
  -- ⟨σ₁, γ₁(b₁)⟩ ⇝* ⟨imσ₁, bv₁⟩
  -- ⟨imσ₁, (x ↦ bv₁, γ₁)(e₁)⟩ ⇝* ⟨σ₃, v₁⟩
  -- ————————————————————————————————————————————
  -- ⟨σ₁, lets x = γ₁(b₁) in γ₁(e₁)⟩ ⇝* ⟨σ₃, v₁⟩
  exists 𝓦₂, σ₃, v₁
  constructor
  . constructor; omega
    apply World.future.trans _ _ _ Hfuture₁
    apply Hfuture₀
  constructor
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
  . apply log_approx_value.antimono
    apply Hsem_value; simp; omega

-- Γ ⊧ n₀ ≤𝑙𝑜𝑔 n₁ : ℕ
-- ——————————————————————————————————
-- Γ ⊧ alloc n₀ ≤𝑙𝑜𝑔 alloc n₁ : ref ℕ
lemma compatibility.alloc₁ :
  ∀ Γ n₀ n₁,
    log_approx Γ n₀ n₁ .nat →
    log_approx Γ (.alloc₁ n₀) (.alloc₁ n₁) (.ref .nat) :=
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
  intros k 𝓦₀ γ₀ γ₁ HsemΓ
  have ⟨HEq₀, HEq₁⟩ := log_approx_env.length _ _ _ _ _ HsemΓ
  have ⟨Hmwf₀, Hmwf₁⟩ := log_approx_env.syntactic.mwf _ _ _ _ _ HsemΓ
  have ⟨HmG₀, HmG₁⟩ := log_approx_env.syntactic.mgrounded _ _ _ _ _ HsemΓ
  have HG₀ : grounded (msubst γ₀ (.alloc₁ n₀)) :=
    by
    apply grounded.under_msubst _ _ HmG₀
    apply typing.dynamic_impl_grounded _ _ _ _ Hτ₀
  have HG₁ : grounded (msubst γ₁ (.alloc₁ n₁)) :=
    by
    apply grounded.under_msubst _ _ HmG₁
    apply typing.dynamic_impl_grounded _ _ _ _ Hτ₁
  simp at HG₀ HG₁
  simp only [log_approx_expr]
  intros j Hindexj σ₀ σ₁ Hsem_store σ₂ v₀ Hvalue₀ Hstep₀
  --
  --
  -- ⟨σ₀, alloc γ₀(n₀)⟩ ⇝ ⟦j⟧ ⟨σ₂, v₀⟩
  -- ——————————————————————————————————
  -- i₀ + i₁ = j
  -- ⟨σ₀, γ₀(n₀)⟩ ⇝ ⟦i₀⟧ ⟨imσ₀, nv₀⟩
  -- ⟨imσ₀, alloc nv₀⟩ ⇝ ⟦i₁⟧ ⟨σ₂, v₀⟩
  simp at Hstep₀
  have ⟨imσ₀, i₀, i₁, nv₀, HEqj, HvalueNat₀, HstepNat₀, Hstep₀⟩ := stepn_indexed.refine.alloc₁.constructor _ _ _ _ _ Hvalue₀ HG₀ Hstep₀
  -- ⟨σ₀, γ₀(n₀)⟩ ⇝ ⟦i₀⟧ ⟨imσ₀, nv₀⟩
  -- Γ ⊧ n₀ ≤𝑙𝑜𝑔 n₁ : ℕ
  -- ————————————————————————————————
  -- ⟨σ₁, γ₁(n₁)⟩ ⇝* ⟨imσ₁, nv₁⟩
  -- (imσ₀, imσ₁) : 𝓦₁
  -- nv₀ = nv₁
  simp only [log_approx_expr] at Hn
  have ⟨𝓦₁, imσ₁, nv₁, Hfuture₀, HstepNat₁, Hsem_store, Hsem_value_nat⟩ := Hn _ _ _ _ HsemΓ i₀ (by omega) _ _ Hsem_store _ _ HvalueNat₀ HstepNat₀
  have ⟨_, Hfuture₀⟩ := Hfuture₀
  have ⟨HvalueNat₀, HvalueNat₁⟩ := log_approx_value.syntactic.value _ _ _ _ _ Hsem_value_nat
  cases HvalueNat₀ <;> try simp at Hsem_value_nat
  case lit nv₀ =>
  cases HvalueNat₁ <;> try simp at Hsem_value_nat
  case lit nv₁ =>
  have ⟨HEqσ₂, _, HEqv₀⟩ := stepn_indexed.refine.alloc₁.eliminator _ _ _ _ _ Hvalue₀ Hstep₀
  rw [← HEqσ₂, HEqv₀]
  --
  --
  -- ⟨σ₁, γ₁(n₁)⟩ ⇝* ⟨imσ₁, nv₁⟩
  -- —————————————————————————————————————————————————————
  -- ⟨σ₁, alloc γ₁(n₁)⟩ ⇝* ⟨nv₁ :: imσ₁, loc imσ₁.length⟩
  exists World.ext 𝓦₁ imσ₀.length imσ₁.length, (.lit nv₁) :: imσ₁, .loc imσ₁.length
  constructor
  . constructor
    . omega
    . apply World.future.trans _ _ _ (World.future.ext _ _ _) Hfuture₀
  constructor
  . simp
    -- left
    apply stepn.trans
    apply stepn_grounded.congruence_under_ctx𝔹 _ _ _ _ _ ctx𝔹.alloc₁ _ HstepNat₁
    apply HG₁
    -- head
    apply stepn.multi _ _ _ _ (stepn.refl _)
    apply step_lvl.mutable _ _ _ _ _ ctx𝕄.hole
    . simp
    . apply head_mutable.alloc₁
  constructor
  . rw [Hsem_value_nat]
    apply log_well_store.alloc _ _ _ _ Hsem_store
  . simp

-- Γ ⊧ l₀ ≤𝑙𝑜𝑔 l₁ : ref ℕ
-- ————————————————————————
-- Γ ⊧ !l₀ ≤𝑙𝑜𝑔 !l₁ : ref ℕ
lemma compatibility.load₁ :
  ∀ Γ l₀ l₁,
    log_approx Γ l₀ l₁ (.ref .nat) →
    log_approx Γ (.load₁ l₀) (.load₁ l₁) .nat :=
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
  intros k 𝓦₀ γ₀ γ₁ HsemΓ
  have ⟨HEq₀, HEq₁⟩ := log_approx_env.length _ _ _ _ _ HsemΓ
  have ⟨Hmwf₀, Hmwf₁⟩ := log_approx_env.syntactic.mwf _ _ _ _ _ HsemΓ
  have ⟨HmG₀, HmG₁⟩ := log_approx_env.syntactic.mgrounded _ _ _ _ _ HsemΓ
  have HG₀ : grounded (msubst γ₀ (.load₁ l₀)) :=
    by
    apply grounded.under_msubst _ _ HmG₀
    apply typing.dynamic_impl_grounded _ _ _ _ Hτ₀
  have HG₁ : grounded (msubst γ₁ (.load₁ l₁)) :=
    by
    apply grounded.under_msubst _ _ HmG₁
    apply typing.dynamic_impl_grounded _ _ _ _ Hτ₁
  simp at HG₀ HG₁
  simp only [log_approx_expr]
  intros j Hindexj σ₀ σ₁ Hsem_store σ₂ v₀ Hvalue₀ Hstep₀
  --
  --
  -- ⟨σ₀, load γ₀(l₀)⟩ ⇝ ⟦j⟧ ⟨σ₂, v₀⟩
  -- ——————————————————————————————————
  -- i₀ + i₁ = j
  -- ⟨σ₀, γ₀(l₀)⟩ ⇝ ⟦i₀⟧ ⟨imσ₀, lv₀⟩
  -- ⟨imσ₀, load lv₀⟩ ⇝ ⟦i₁⟧ ⟨σ₂, v₀⟩
  simp at Hstep₀
  have ⟨imσ₀, i₀, i₁, lv₀, HEqj, HvalueLoc₀, HstepLoc₀, Hstep₀⟩ := stepn_indexed.refine.load₁.constructor _ _ _ _ _ Hvalue₀ HG₀ Hstep₀
  -- ⟨σ₀, γ₀(l₀)⟩ ⇝ ⟦i₀⟧ ⟨imσ₀, lv₀⟩
  -- Γ ⊧ l₀ ≤𝑙𝑜𝑔 l₁ : ℕ
  -- ————————————————————————————————
  -- ⟨σ₁, γ₁(l₁)⟩ ⇝* ⟨imσ₁, lv₁⟩
  -- (imσ₀, imσ₁) : 𝓦₁
  -- 𝓦₁ lv₀ lv₁
  simp only [log_approx_expr] at Hl
  have ⟨𝓦₁, imσ₁, lv₁, Hfuture₀, HstepLoc₁, Hsem_store, Hsem_value_loc⟩ := Hl _ _ _ _ HsemΓ i₀ (by omega) _ _ Hsem_store _ _ HvalueLoc₀ HstepLoc₀
  have ⟨_, Hfuture₀⟩ := Hfuture₀
  have ⟨HvalueLoc₀, HvalueLoc₁⟩ := log_approx_value.syntactic.value _ _ _ _ _ Hsem_value_loc
  cases HvalueLoc₀ <;> try simp at Hsem_value_loc
  case loc lv₀ =>
  cases HvalueLoc₁ <;> try simp at Hsem_value_loc
  case loc lv₁ =>
  have ⟨n, Hbinds₀, Hbinds₁⟩ := Hsem_store.right _ _ Hsem_value_loc
  have ⟨HEqσ₂, _, HEqv₀⟩ := stepn_indexed.refine.load₁.eliminator _ _ _ _ _ _ Hvalue₀ Hbinds₀ Hstep₀
  rw [← HEqσ₂, HEqv₀]
  --
  --
  -- ⟨σ₁, γ₁(l₁)⟩ ⇝* ⟨imσ₁, lv₁⟩
  -- ———————————————————————————————————
  -- ⟨σ₁, !γ₁(l₁)⟩ ⇝* ⟨imσ₁, imσ₁(lv₁)⟩
  exists 𝓦₁, imσ₁, .lit n
  constructor
  . constructor; omega
    apply Hfuture₀
  constructor
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

-- Γ ⊧ l₀ ≤𝑙𝑜𝑔 l₁ : ref ℕ
-- Γ ⊧ n₀ ≤𝑙𝑜𝑔 n₁ : ℕ
-- —————————————————————————————————————
-- Γ ⊧ (l₀ := n₀) ≤𝑙𝑜𝑔 (l₁ := n₁) : unit
lemma compatibility.store₁ :
  ∀ Γ l₀ l₁ n₀ n₁,
    log_approx Γ l₀ l₁ (.ref .nat) →
    log_approx Γ n₀ n₁ .nat →
    log_approx Γ (.store₁ l₀ n₀) (.store₁ l₁ n₁) .unit :=
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
  intros k 𝓦₀ γ₀ γ₁ HsemΓ
  have ⟨HEq₀, HEq₁⟩ := log_approx_env.length _ _ _ _ _ HsemΓ
  have ⟨Hmwf₀, Hmwf₁⟩ := log_approx_env.syntactic.mwf _ _ _ _ _ HsemΓ
  have ⟨HmG₀, HmG₁⟩ := log_approx_env.syntactic.mgrounded _ _ _ _ _ HsemΓ
  have HG₀ : grounded (msubst γ₀ (.store₁ l₀ n₀)) :=
    by
    apply grounded.under_msubst _ _ HmG₀
    apply typing.dynamic_impl_grounded _ _ _ _ Hτ₀
  have HG₁ : grounded (msubst γ₁ (.store₁ l₁ n₁)) :=
    by
    apply grounded.under_msubst _ _ HmG₁
    apply typing.dynamic_impl_grounded _ _ _ _ Hτ₁
  simp at HG₀ HG₁
  simp only [log_approx_expr]
  intros j Hindexj σ₀ σ₁ Hsem_store σ₂ v₀ Hvalue₀ Hstep₀
  --
  --
  -- ⟨σ₀, γ₀(l₀) := γ₀(n₀)⟩ ⇝ ⟦j⟧ ⟨σ₂, v₀⟩
  -- ——————————————————————————————————————
  -- i₀ + i₁ + i₂ = j
  -- ⟨σ₀, γ₀(l₀)⟩ ⇝ ⟦i₀⟧ ⟨imσ₀, lv₀⟩
  -- ⟨imσ₀, γ₀(n₀)⟩ ⇝ ⟦i₁⟧ ⟨imσ₂, nv₀⟩
  -- ⟨imσ₂, lv₀ := nv₀⟩ ⇝ ⟦i₂⟧ ⟨σ₂, v₀⟩
  simp at Hstep₀
  have ⟨imσ₀, imσ₂, i₀, i₁, i₂, lv₀, nv₀, HEqj, HvalueLoc₀, HvalueNat₀, HstepLoc₀, HstepNat₀, Hstep₀⟩ := stepn_indexed.refine.store₁.constructor _ _ _ _ _ _ Hvalue₀ HG₀ Hstep₀
  -- ⟨σ₀, γ₀(l₀)⟩ ⇝ ⟦i₀⟧ ⟨imσ₀, lv₀⟩
  -- Γ ⊧ l₀ ≤𝑙𝑜𝑔 l₁ : ℕ
  -- ————————————————————————————————
  -- ⟨σ₁, γ₁(l₁)⟩ ⇝* ⟨imσ₁, lv₁⟩
  -- (imσ₀, imσ₁) : 𝓦₁
  -- 𝓦₁ lv₀ lv₁
  simp only [log_approx_expr] at Hl
  have ⟨𝓦₁, imσ₁, lv₁, Hfuture₀, HstepLoc₁, Hsem_store, Hsem_value_loc⟩ := Hl _ _ _ _ HsemΓ i₀ (by omega) _ _ Hsem_store _ _ HvalueLoc₀ HstepLoc₀
  have ⟨_, Hfuture₀⟩ := Hfuture₀
  have ⟨HvalueLoc₀, HvalueLoc₁⟩ := log_approx_value.syntactic.value _ _ _ _ _ Hsem_value_loc
  cases HvalueLoc₀ <;> try simp at Hsem_value_loc
  case loc lv₀ =>
  cases HvalueLoc₁ <;> try simp at Hsem_value_loc
  case loc lv₁ =>
  -- ⟨imσ₀, γ₀(n₀)⟩ ⇝ ⟦i₁⟧ ⟨imσ₂, nv₀⟩
  -- Γ ⊧ n₀ ≤𝑙𝑜𝑔 n₁ : ℕ
  -- ————————————————————————————————
  -- ⟨imσ₁, γ₁(n₁)⟩ ⇝* ⟨imσ₃, nv₁⟩
  -- (imσ₂, imσ₃) : 𝓦₂
  -- nv₀ = nv₁
  simp only [log_approx_expr] at Hn
  have HsemΓ : log_approx_env (k - i₀, 𝓦₁) γ₀ γ₁ Γ :=
    by
    apply log_approx_env.antimono; apply HsemΓ
    constructor; omega; apply Hfuture₀
  have ⟨𝓦₂, imσ₃, nv₁, Hfuture₁, HstepNat₁, Hsem_store, Hsem_value_nat⟩ := Hn (k - i₀) 𝓦₁ _ _ HsemΓ i₁ (by omega) _ _ Hsem_store _ _ HvalueNat₀ HstepNat₀
  have ⟨_, Hfuture₁⟩ := Hfuture₁
  have ⟨HvalueNat₀, HvalueNat₁⟩ := log_approx_value.syntactic.value _ _ _ _ _ Hsem_value_nat
  cases HvalueNat₀ <;> try simp at Hsem_value_nat
  case lit nv₀ =>
  cases HvalueNat₁ <;> try simp at Hsem_value_nat
  case lit nv₁ =>
  have Hsem_value_loc := Hfuture₁ _ _ Hsem_value_loc
  have ⟨n, Hbinds₀, Hbinds₁⟩ := Hsem_store.right _ _ Hsem_value_loc
  have ⟨imσ₄, Hpatch₀⟩ : ∃ imσ₄, patch lv₀ (.lit nv₀) imσ₂ imσ₄ :=
    by
    simp [← setr_exists_iff_index_lt_length, getr_exists_iff_index_lt_length]
    exists .lit n
  have ⟨imσ₅, Hpatch₁⟩ : ∃ imσ₅, patch lv₁ (.lit nv₁) imσ₃ imσ₅ :=
    by
    simp [← setr_exists_iff_index_lt_length, getr_exists_iff_index_lt_length]
    exists .lit n
  have ⟨HEqσ₂, _, HEqv₀⟩ := stepn_indexed.refine.store₁.eliminator _ _ _ _ _ _ _ Hvalue₀ Hpatch₀ Hstep₀
  rw [← HEqσ₂, HEqv₀]
  --
  --
  -- ⟨σ₁, γ₁(l₁)⟩ ⇝* ⟨imσ₁, lv₁⟩
  -- ⟨imσ₁, γ₁(n₁)⟩ ⇝* ⟨imσ₃, nv₁⟩
  -- ————————————————————————————————————————————————
  -- ⟨σ₁, γ₁(l₁) := γ₁(n₁)⟩ ⇝* ⟨(lv₁ ↦ nv₁)imσ₃, ()⟩
  exists 𝓦₂, imσ₅, .unit
  constructor
  . constructor; omega
    apply World.future.trans _ _ _ Hfuture₁
    apply Hfuture₀
  constructor
  . simp
    -- left
    apply stepn.trans
    apply stepn_grounded.congruence_under_ctx𝔹 _ _ _ _ _ (ctx𝔹.storel₁ _ _) _ HstepLoc₁
    . apply lc.under_msubst _ _ _ Hmwf₁ (typing.regular _ _ _ _ _ HτNat₁)
    . apply HG₁.left
    -- right
    apply stepn.trans
    apply stepn_grounded.congruence_under_ctx𝔹 _ _ _ _ _ (ctx𝔹.storer₁ _ _) _ HstepNat₁
    . apply value.loc
    . apply HG₁.right
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

lemma compatibility.fix₁.induction :
  ∀ k 𝓦 f₀ f₁ τ𝕒 τ𝕓,
    log_approx_value (k, 𝓦) f₀ f₁ (.arrow (.arrow τ𝕒 τ𝕓 ⊥) (.arrow τ𝕒 τ𝕓 ⊥) ⊥) →
    log_approx_value (k, 𝓦)
      (.lam (.app₁ (.app₁ f₀ (.fix₁ f₀)) (.bvar 0)))
      (.lam (.app₁ (.app₁ f₁ (.fix₁ f₁)) (.bvar 0)))
    (.arrow τ𝕒 τ𝕓 ⊥) :=
  by
  intros k 𝓦₀ f₀ f₁ τ𝕒 τ𝕓 Hsem_value_fix
  have ⟨HvalueFix₀, HvalueFix₁⟩ := log_approx_value.syntactic.value _ _ _ _ _ Hsem_value_fix
  have ⟨HwfFix₀, HwfFix₁⟩ := log_approx_value.syntactic.wf _ _ _ _ _ Hsem_value_fix
  have ⟨HGFix₀, HGFix₁⟩ := log_approx_value.syntactic.grounded _ _ _ _ _ Hsem_value_fix
  have HwfFun₀ : wf (.lam (.app₁ (.app₁ f₀ (.fix₁ f₀)) (.bvar 0))) :=
    by
    constructor
    . simp; apply lc.inc; apply HwfFix₀.left; omega
    . simp; apply HwfFix₀.right
  have HwfFun₁ : wf (.lam (.app₁ (.app₁ f₁ (.fix₁ f₁)) (.bvar 0))) :=
    by
    constructor
    . simp; apply lc.inc; apply HwfFix₁.left; omega
    . simp; apply HwfFix₁.right
  induction k
  case zero =>
    simp only [log_approx_value]
    constructor; apply HwfFun₀
    constructor; simp; apply HGFix₀
    constructor; apply HwfFun₁
    constructor; simp; apply HGFix₁
    intro z 𝓦₁ argv₀ argv₁ Hfuture₀ Hsem_value_arg
    have ⟨_, Hfuture₀⟩ := Hfuture₀
    simp only [log_approx_expr]
    intro j Hindexj; omega
  case succ k IH =>
    simp only [log_approx_value]
    constructor; apply HwfFun₀
    constructor; simp; apply HGFix₀
    constructor; apply HwfFun₁
    constructor; simp; apply HGFix₁
    intro s 𝓦₁ argv₀ argv₁ Hfuture₀ Hsem_value_arg
    have ⟨_, Hfuture₀⟩ := Hfuture₀
    have ⟨HvalueArg₀, HvalueArg₁⟩ := log_approx_value.syntactic.value _ _ _ _ _ Hsem_value_arg
    have ⟨HGArg₀, HGArg₁⟩ := log_approx_value.syntactic.grounded _ _ _ _ _ Hsem_value_arg
    simp only [log_approx_expr]
    intros j Hindexj σ₀ σ₁ Hsem_store σ₂ v₀ Hvalue₀ Hstep₀
    --
    --
    -- ⟨σ₀, (λx.f₀ @ fix f₀ @ x) @ argv₀⟩ ⇝ ⟦j⟧ ⟨σ₂, v₀⟩
    -- ——————————————————————————————————————————————————————
    -- i + 2 = j
    -- ⟨σ₀, f₀ @ (λx.f₀ @ fix f₀ @ x) @ argv₀⟩ ⇝ ⟦i⟧ ⟨σ₂, v₀⟩
    have ⟨i, HEqj, Hstep₀⟩ := stepn_indexed.refine.fix₁.eliminator _ _ _ _ _ _ HvalueFix₀ HvalueArg₀ Hvalue₀ (by simp; apply HGFix₀) Hstep₀
    --
    --
    -- ⟨σ₀, f₀ @ (λx.f₀ @ fix f₀ @ x) @ argv₀⟩ ⇝ ⟦i⟧ ⟨σ₂, v₀⟩
    -- ——————————————————————————————————————————————————————
    -- i₀ + i₁ = i
    -- ⟨σ₀, f₀ @ (λx.f₀ @ fix f₀ @ x)⟩ ⇝ ⟦i₀⟧ ⟨imσ₀, fv₀⟩
    -- ⟨imσ₀, fv₀ @ argv₀⟩ ⇝ ⟦i₁⟧ ⟨σ₂, v₀⟩
    have ⟨imσ₀, _, i₀, z, i₁, fv₀, _, HEqj, HvalueFun₀, _, HstepFun₀, HstepArg₀, Hstep₀⟩ := stepn_indexed.refine.app₁.constructor _ _ _ _ _ _ Hvalue₀ (
      by simp; constructor; apply HGFix₀; apply HGArg₀
    ) Hstep₀
    have ⟨HEqσ, HEqv, Hz⟩ := stepn_indexed.value_impl_termination _ _ _ _ _ HvalueArg₀ HstepArg₀
    rw [← HEqσ, ← HEqv] at Hstep₀
    --
    --
    -- (k + 1, 𝓦₀, f₀, f₁) ∈ 𝓥⟦(τ𝕒 → τ𝕓) → (τ𝕒 → τ𝕓)⟧
    -- (k, 𝓦₀, λx.f₀ @ fix f₀ @ x, λx.f₁ @ fix f₁ @ x) ∈ 𝓥⟦τ𝕒 → τ𝕓⟧
    -- ———————————————————————————————————————————————————————————————————————————
    -- (k, 𝓦₁, f₀ @ (λx.f₀ @ fix f₀ @ x), f₁ @ (λx.f₁ @ fix f₁ @ x)) ∈ 𝓔⟦τ𝕒 → τ𝕓⟧
    have Hsem_expr_fun :
      log_approx_expr (k, 𝓦₁)
        (.app₁ f₀ (.lam (.app₁ (.app₁ f₀ (.fix₁ f₀)) (.bvar 0))))
        (.app₁ f₁ (.lam (.app₁ (.app₁ f₁ (.fix₁ f₁)) (.bvar 0))))
      (.arrow τ𝕒 τ𝕓 ⊥) :=
      by
      apply log_approx_value.apply
      apply log_approx_value.antimono; apply Hsem_value_fix
      constructor; omega; apply Hfuture₀
      apply log_approx_value.antimono; apply IH (log_approx_value.antimono _ _ _ _ _ _ _ Hsem_value_fix (by simp))
      constructor; omega; apply Hfuture₀
    --
    --
    -- ⟨σ₀, f₀ @ (λx.f₀ @ fix f₀ @ x)⟩ ⇝ ⟦i₀⟧ ⟨imσ₀, fv₀⟩
    -- (k, 𝓦₁, f₀ @ (λx.f₀ @ fix f₀ @ x), f₁ @ (λx.f₁ @ fix f₁ @ x)) ∈ 𝓔⟦τ𝕒 → τ𝕓⟧
    -- ———————————————————————————————————————————————————————————————————————————
    -- ⟨σ₁, f₁ @ (λx.f₁ @ fix f₁ @ x)⟩ ⇝* ⟨imσ₁, fv₁⟩
    -- (imσ₀, imσ₁) : 𝓦₂
    -- (k - i₀, 𝓦₂, fv₀, fv₁) ∈ 𝓥⟦τ𝕒 → τ𝕓⟧
    simp only [log_approx_expr] at Hsem_expr_fun
    have ⟨𝓦₂, imσ₁, fv₁, Hfuture₁, HstepFun₁, Hsem_store, Hsem_value_fun⟩ := Hsem_expr_fun i₀ (by omega) _ _ Hsem_store _ _ HvalueFun₀ HstepFun₀
    have ⟨_, Hfuture₁⟩ := Hfuture₁
    --
    --
    -- (k - i₀, 𝓦₂, fv₀, fv₁) ∈ 𝓥⟦τ𝕒 → τ𝕓⟧
    -- (s, 𝓦₁, argv₀, argv₁) ∈ 𝓥⟦τ𝕒⟧
    -- ——————————————————————————————————————————————————
    -- (s - i₀ - 1, 𝓦₂, fv₀ @ argv₀, fv₁ @ argv₁) ∈ 𝓔⟦τ𝕓⟧
    have Hsem_value_fun : log_approx_value (s - i₀ - 1, 𝓦₂) fv₀ fv₁ (τ𝕒.arrow τ𝕓 ⊥) :=
      log_approx_value.antimono _ _ _ _ _ _ _ Hsem_value_fun (by constructor; omega; simp)
    have Hsem_value_arg : log_approx_value (s - i₀ - 1, 𝓦₂) argv₀ argv₁ τ𝕒 :=
      log_approx_value.antimono _ _ _ _ _ _ _ Hsem_value_arg (by constructor; omega; apply Hfuture₁)
    have Hsem_expr := log_approx_value.apply _ _ _ _ _ _ _ _ Hsem_value_fun Hsem_value_arg
    --
    --
    -- (s - i₀ - 1, 𝓦₂, fv₀ @ argv₀, fv₁ @ argv₁) ∈ 𝓔⟦τ𝕓⟧
    -- ⟨imσ₀, fv₀ @ argv₀⟩ ⇝ ⟦i₁⟧ ⟨σ₂, v₀⟩
    -- —————————————————————————————————————————————
    -- ⟨imσ₁, fv₁ @ argv₁⟩ ⇝* ⟨σ₃, v₁⟩
    -- (σ₂, σ₃) : 𝓦₃
    -- (s - i₀ - i₁ - 1, 𝓦₃, v₀, v₁) ∈ 𝓥⟦τ𝕓⟧
    simp only [log_approx_expr] at Hsem_expr
    have ⟨𝓦₃, σ₃, v₁, Hfuture₂, Hstep₁, Hsem_store, Hsem_value⟩ := Hsem_expr i₁ (by omega) _ _ Hsem_store _ _ Hvalue₀ Hstep₀
    have ⟨_, Hfuture₂⟩ := Hfuture₂
    --
    --
    -- ⟨σ₁, f₁ @ (λx.f₁ @ fix f₁ @ x)⟩ ⇝* ⟨imσ₁, fv₁⟩
    -- ⟨imσ₁, fv₁ @ argv₁⟩ ⇝* ⟨σ₃, v₁⟩
    -- ——————————————————————————————————————————————
    -- ⟨σ₁, (λx.f₁ @ fix f₁ @ x) @ argv₁⟩ ⇝* ⟨σ₃, v₁⟩
    exists 𝓦₃, σ₃, v₁
    constructor
    . constructor; omega
      apply World.future.trans _ _ _ Hfuture₂
      apply Hfuture₁
    constructor
    . -- head₀
      apply stepn.multi
      apply step_lvl.pure _ _ _ _ ctx𝕄.hole
      . simp; constructor
        . apply lc.inc; apply lc.value _ HvalueFix₁; omega
        . apply lc.value _ HvalueArg₁
      . apply head_pure.app₁; apply HvalueArg₁
      simp [identity.opening _ _ _ (lc.value _ HvalueFix₁)]
      -- head₁
      apply stepn.multi
      apply step_grounded.congruence_under_ctx𝔹 _ _ _ _ _ (ctx𝔹.appl₁ _ (lc.value _ HvalueArg₁))
      simp; apply HGFix₁
      apply step_grounded.congruence_under_ctx𝔹 _ _ _ _ _ (ctx𝔹.appr₁ _ HvalueFix₁)
      simp; apply HGFix₁
      apply step_lvl.pure _ _ _ _ ctx𝕄.hole
      . apply lc.value _ HvalueFix₁
      . apply head_pure.fix₁; apply HvalueFix₁
      -- left
      apply stepn.trans
      apply stepn_grounded.congruence_under_ctx𝔹 _ _ _ _ _ (ctx𝔹.appl₁ _ (lc.value _ HvalueArg₁))
      simp; apply HGFix₁; apply HstepFun₁
      -- head₂
      apply Hstep₁
    constructor
    . apply Hsem_store
    . apply log_approx_value.antimono
      apply Hsem_value; simp; omega

-- Γ ⊧ f₀ ≤𝑙𝑜𝑔 f₁ : (τ𝕒 → τ𝕓) → (τ𝕒 → τ𝕓)
-- ——————————————————————————————————————
-- Γ ⊧ fix f₀ ≤𝑙𝑜𝑔 fix f₁ : τ𝕒 → τ𝕓
lemma compatibility.fix₁ :
  ∀ Γ f₀ f₁ τ𝕒 τ𝕓,
    log_approx Γ f₀ f₁ (.arrow (.arrow τ𝕒 τ𝕓 ⊥) (.arrow τ𝕒 τ𝕓 ⊥) ⊥) →
    log_approx Γ (.fix₁ f₀) (.fix₁ f₁) (.arrow τ𝕒 τ𝕓 ⊥) :=
  by
  intros Γ f₀ f₁ τ𝕒 τ𝕓 Hf
  have ⟨HτFix₀, HτFix₁, Hf⟩ := Hf
  have Hτ₀ : typing Γ 𝟚 (.fix₁ f₀) (.arrow τ𝕒 τ𝕓 ⊥) ⊥ := by apply typing.fix₁; simp; rfl; apply HτFix₀
  have Hτ₁ : typing Γ 𝟚 (.fix₁ f₁) (.arrow τ𝕒 τ𝕓 ⊥) ⊥ := by apply typing.fix₁; simp; rfl; apply HτFix₁
  constructor; apply Hτ₀
  constructor; apply Hτ₁
  intros k 𝓦₀ γ₀ γ₁ HsemΓ
  have ⟨Hmwf₀, Hmwf₁⟩ := log_approx_env.syntactic.mwf _ _ _ _ _ HsemΓ
  have ⟨HmG₀, HmG₁⟩ := log_approx_env.syntactic.mgrounded _ _ _ _ _ HsemΓ
  have HG₀ : grounded (msubst γ₀ (.fix₁ f₀)) :=
    by
    apply grounded.under_msubst _ _ HmG₀
    apply typing.dynamic_impl_grounded _ _ _ _ Hτ₀
  have HG₁ : grounded (msubst γ₁ (.fix₁ f₁)) :=
    by
    apply grounded.under_msubst _ _ HmG₁
    apply typing.dynamic_impl_grounded _ _ _ _ Hτ₁
  simp at HG₀ HG₁
  simp only [log_approx_expr]
  intros j Hindexj σ₀ σ₁ Hsem_store σ₂ v₀ Hvalue₀ Hstep₀
  --
  --
  -- ⟨σ₀, fix γ₀(f₀)⟩ ⇝ ⟦j⟧ ⟨σ₂, v₀⟩
  -- ———————————————————————————————
  -- i₀ + 1 = j
  -- ⟨σ₀, γ₀(f₀)⟩ ⇝ ⟦i₀⟧ ⟨σ₂, fv₀⟩
  -- v₀ = λx.fv₀ @ fix fv₀ @ x
  simp at Hstep₀
  have ⟨i₀, fv₀, HEqj, HvalueFix₀, HstepFix₀, HEqv₀⟩ := stepn_indexed.refine.fix₁.constructor _ _ _ _ _ Hvalue₀ HG₀ Hstep₀
  rw [HEqv₀]
  --
  --
  -- ⟨σ₀, γ₀(f₀)⟩ ⇝ ⟦i₀⟧ ⟨σ₂, fv₀⟩
  -- Γ ⊧ f₀ ≤𝑙𝑜𝑔 f₁ : (τ𝕒 → τ𝕓) → (τ𝕒 → τ𝕓)
  -- ——————————————————————————————————————————————————
  -- ⟨σ₀, γ₁(f₁)⟩ ⇝* ⟨σ₃, fv₁⟩
  -- (σ₂, σ₃) : 𝓦₁
  -- (k - i₀, 𝓦₁, fv₀, fv₁) ∈ 𝓥⟦(τ𝕒 → τ𝕓) → (τ𝕒 → τ𝕓)⟧
  simp only [log_approx_expr] at Hf
  have ⟨𝓦₁, σ₃, fv₁, Hfuture₀, HstepFix₁, Hsem_store, Hsem_value_fix⟩ := Hf _ _ _ _ HsemΓ i₀ (by omega) _ _ Hsem_store _ _ HvalueFix₀ HstepFix₀
  have ⟨HvalueFix₀, HvalueFix₁⟩ := log_approx_value.syntactic.value _ _ _ _ _ Hsem_value_fix
  have ⟨_, Hfuture₀⟩ := Hfuture₀
  --
  --
  -- ⟨σ₀, γ₁(f₁)⟩ ⇝* ⟨σ₃, fv₁⟩
  -- ———————————————————————————————————————————————
  -- ⟨σ₀, fix γ₁(f₁)⟩ ⇝* ⟨σ₃, λx.fv₁ @ fix fv₁ @ x⟩
  exists 𝓦₁, σ₃, .lam (.app₁ (.app₁ fv₁ (.fix₁ fv₁)) (.bvar 0))
  constructor
  . constructor; omega
    apply Hfuture₀
  constructor
  . -- left
    simp
    apply stepn.trans
    apply stepn_grounded.congruence_under_ctx𝔹 _ _ _ _ _ ctx𝔹.fix₁ HG₁ HstepFix₁
    -- head
    apply stepn.multi _ _ _ _ (stepn.refl _)
    apply step_lvl.pure _ _ _ _ ctx𝕄.hole
    simp; apply lc.value; apply HvalueFix₁
    apply head_pure.fix₁; apply HvalueFix₁
  constructor
  . apply Hsem_store
  . apply compatibility.fix₁.induction
    apply log_approx_value.antimono
    apply Hsem_value_fix
    constructor; omega; simp
