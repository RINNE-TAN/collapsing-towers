import CollapsingTowers.TwoLevelRec.LogicalEquiv.Fundamental

mutual
lemma log_approx_value.trans (k : Nat) (v₀ v₁ v₂ : Expr) (τ : Ty) :
    log_approx_value k v₀ v₁ τ →
    (∀ k, log_approx_value k v₁ v₂ τ) →
    log_approx_value k v₀ v₂ τ :=
    match τ with
    | .nat =>
      by
      intros Hsem_value₀ Hsem_value₁
      cases v₀ <;> try simp at Hsem_value₀
      cases v₁ <;> try simp at Hsem_value₀
      cases v₂ <;> try simp at Hsem_value₁
      simp; omega
    | .arrow τ𝕒 τ𝕓 φ =>
      by
      intros Hsem_value₀ Hsem_value₁
      cases v₀ <;> try simp at Hsem_value₀
      case lam e₀ =>
      cases v₁ <;> try simp at Hsem_value₀
      case lam e₁ =>
      cases v₂ <;> try simp at Hsem_value₁
      case lam e₂ =>
      cases φ <;> simp only [log_approx_value] at Hsem_value₀ Hsem_value₁ <;> try contradiction
      simp only [log_approx_value]
      have ⟨Hτ₀, Hτ₁, Hsem_expr₀⟩ := Hsem_value₀
      have ⟨Hτ₁, Hτ₂, _⟩ := Hsem_value₁ 0
      constructor; apply Hτ₀
      constructor; apply Hτ₂
      intros j Hindexj argv₀ argv₁ Hsem_value_arg₀
      have ⟨HvalueArg₀, HvalueArg₁⟩ := log_approx_value.syntactic.value _ _ _ _ Hsem_value_arg₀
      have ⟨HτArg₀, HτArg₁⟩ := log_approx_value.syntactic.typing _ _ _ _ Hsem_value_arg₀
      apply log_approx_expr.trans; apply Hsem_expr₀
      apply Hindexj; apply Hsem_value_arg₀
      intros k
      have ⟨Hτ₁, Hτ₂, Hsem_expr₁⟩ := Hsem_value₁ k
      apply Hsem_expr₁; rfl
      apply log_approx_value.fundamental
      apply HvalueArg₁; apply HτArg₁
    | .fragment _ => by simp
    | .rep _ => by simp

termination_by (τ, k)
decreasing_by apply Prod.Lex.left; simp; omega

lemma log_approx_expr.trans :
  ∀ k e₀ e₁ e₂ τ,
    log_approx_expr k e₀ e₁ τ →
    (∀ k, log_approx_expr k e₁ e₂ τ) →
    log_approx_expr k e₀ e₂ τ :=
  by
  intros k e₀ e₁ e₂ τ Hsem_expr₀ Hsem_expr₁
  cases k
  case zero => simp
  case succ k =>
    simp only [log_approx_expr] at Hsem_expr₀ Hsem_expr₁
    simp only [log_approx_expr]
    intros i₀ Hindexi₀ v₀ Hvalue₀ Hstep₀
    have ⟨v₁, Hstep₁, Hsem_value₀⟩ := Hsem_expr₀ _ Hindexi₀ _ Hvalue₀ Hstep₀
    have ⟨Hvalue₀, Hvalue₁⟩ := log_approx_value.syntactic.value _ _ _ _ Hsem_value₀
    have ⟨i₁, Hstep₁⟩ := stepn_impl_stepn_indexed _ _ Hstep₁
    have ⟨v₂, Hstep₂, Hsem_value₁⟩ := Hsem_expr₁ (i₁ + 1) i₁ (by omega) _ Hvalue₁ Hstep₁
    have ⟨Hvalue₁, Hvalue₂⟩ := log_approx_value.syntactic.value _ _ _ _ Hsem_value₁
    exists v₂
    constructor; apply Hstep₂
    apply log_approx_value.trans; apply Hsem_value₀
    intros k
    have ⟨v₃, Hstep₃, Hsem_value₂⟩ := Hsem_expr₁ (k + i₁ + 1) i₁ (by omega) _ Hvalue₁ Hstep₁
    have ⟨Hvalue₁, Hvalue₃⟩ := log_approx_value.syntactic.value _ _ _ _ Hsem_value₂
    rw [stepn.unique_normal_forms _ _ _ Hstep₂ Hstep₃ Hvalue₂ Hvalue₃]
    apply log_approx_value.antimono
    apply Hsem_value₂; omega

termination_by k _ _ _ τ => (τ, k + 1)
decreasing_by apply Prod.Lex.right; omega
end

-- Γ ⊧ e₀ ≤𝑙𝑜𝑔 e₁ : τ
-- Γ ⊧ e₁ ≤𝑙𝑜𝑔 e₂ : τ
-- ——————————————————
-- Γ ⊧ e₀ ≤𝑙𝑜𝑔 e₂ : τ
theorem log_approx.trans :
  ∀ Γ e₀ e₁ e₂ τ,
    log_approx Γ e₀ e₁ τ →
    log_approx Γ e₁ e₂ τ →
    log_approx Γ e₀ e₂ τ :=
  by
  intros Γ e₀ e₁ e₂ τ H₀ H₁
  have ⟨Hτ₀, Hτ₁, H₀⟩ := H₀
  have ⟨Hτ₁, Hτ₂, H₁⟩ := H₁
  constructor; apply Hτ₀
  constructor; apply Hτ₂
  intros k γ₀ γ₁ HsemΓ
  have ⟨HτΓ₀, HτΓ₁⟩ := log_approx_env.syntactic.typing _ _ _ _ HsemΓ
  apply log_approx_expr.trans
  apply H₀; apply HsemΓ
  intro k; apply H₁
  apply log_approx_env.fundamental
  apply HτΓ₁
