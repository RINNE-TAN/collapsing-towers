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
  constructor
  . simp
  constructor
  . apply stepn.refl
  constructor
  . rw [← HEqσ]; apply Hsem_store
  . rw [← HEqv, Hz]; apply Hsem_value

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
  constructor
  . simp
  constructor
  . simp; apply stepn.refl
  constructor
  . rw [← HEqσ]; apply Hsem_store
  . simp [← HEqv, Hz]

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
  constructor
  . simp
  constructor
  . simp; apply stepn.refl
  constructor
  . rw [← HEqσ]; apply Hsem_store
  . simp [← HEqv, Hz]
