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
  admit
