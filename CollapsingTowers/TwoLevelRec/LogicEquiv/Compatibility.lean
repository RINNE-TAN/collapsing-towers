import CollapsingTowers.TwoLevelRec.LogicEquiv.LogicRelation

-- Γ ⊧ x ≤𝑙𝑜𝑔 x : Γ(x)
lemma compatibility.fvar :
  ∀ Γ x τ,
    binds x (τ, 𝟙) Γ →
    wbt 𝟙 τ →
    logic_rel_typing Γ (.fvar x) (.fvar x) τ :=
  by
  intros Γ x τ Hbinds Hwbt
  constructor; apply typing.fvar; apply Hbinds; apply Hwbt
  constructor; apply typing.fvar; apply Hbinds; apply Hwbt
  intros k γ₀ γ₁ HsemΓ
  simp only [logic_rel_expr]
  intros z Hindexz v₀ Hvalue₀ Hstep₀
  exists multi_subst γ₁ (.fvar x)
  constructor
  . apply pure_stepn.refl
  . have Hsem_value := logic_rel_env.binds_logic_rel_value _ _ _ _ _ _ HsemΓ Hbinds
    have ⟨Hvalue₀, Hvalue₁⟩ := logic_rel_value.syntactic.value _ _ _ _ Hsem_value
    have ⟨HEqv, Hz⟩ := pure_stepn_indexed.value_impl_termination _ _ _ Hvalue₀ Hstep₀
    rw [← HEqv, Hz]; apply Hsem_value

-- Γ ⊧ n ≤𝑙𝑜𝑔 n : ℕ
lemma compatibility.lit :
  ∀ Γ n, logic_rel_typing Γ (.lit n) (.lit n) .nat :=
  by
  intros _ n
  constructor; apply typing.lit
  constructor; apply typing.lit
  intros k γ₀ γ₁ semΓ
  simp only [logic_rel_expr]
  intros z Hindexz v₀ Hvalue₀ Hstep₀
  exists .lit n
  constructor
  . simp; apply pure_stepn.refl
  . simp at Hstep₀
    have ⟨HEqv, Hz⟩ := pure_stepn_indexed.value_impl_termination _ _ _ (value.lit n) Hstep₀
    simp [← HEqv, Hz]

-- x ↦ τ𝕒, Γ ⊧ e₀ ≤𝑙𝑜𝑔 e₁ : τ𝕓
-- ——————————————————————————————
-- Γ ⊧ λx.e₀ ≤𝑙𝑜𝑔 λx.e₁ : τ𝕒 → τ𝕓
lemma compatibility.lam :
  ∀ Γ e₀ e₁ τ𝕒 τ𝕓,
    wbt 𝟙 τ𝕒 →
    closed_at e₀ Γ.length →
    closed_at e₁ Γ.length →
    logic_rel_typing ((τ𝕒, 𝟙) :: Γ) ({0 ↦ Γ.length} e₀) ({0 ↦ Γ.length} e₁) τ𝕓 →
    logic_rel_typing Γ (.lam e₀) (.lam e₁) (.arrow τ𝕒 τ𝕓 ∅) :=
  by
  intros Γ e₀ e₁ τ𝕒 τ𝕓 Hwbt Hclosed₀ Hclosed₁ He
  have ⟨Hτ₀, Hτ₁, He⟩ := He
  have Hτ₀ : typing Γ 𝟙 (.lam e₀) (.arrow τ𝕒 τ𝕓 ∅) ∅ := by apply typing.lam; apply Hτ₀; apply Hwbt; apply Hclosed₀
  have Hτ₁ : typing Γ 𝟙 (.lam e₁) (.arrow τ𝕒 τ𝕓 ∅) ∅ := by apply typing.lam; apply Hτ₁; apply Hwbt; apply Hclosed₁
  constructor; apply Hτ₀
  constructor; apply Hτ₁
  all_goals admit
