import Instar.TwoLevelBasic.LogicalEquiv.Fundamental

mutual
lemma log_equiv_value.trans
  (v₀ v₁ v₂ : Expr) (τ : Ty) :
    log_equiv_value v₀ v₁ τ →
    log_equiv_value v₁ v₂ τ →
    log_equiv_value v₀ v₂ τ :=
  match τ with
  | .nat =>
    by
    intros Hsem_value₀ Hsem_value₁
    cases v₀ <;> try simp at Hsem_value₀
    cases v₁ <;> try simp at Hsem_value₀
    cases v₂ <;> try simp at Hsem_value₁
    simp; omega
  | .arrow τ𝕒 τ𝕓 ε =>
    by
    intros Hsem_value₀ Hsem_value₁
    cases v₀ <;> try simp at Hsem_value₀
    case lam e₀ =>
    cases v₁ <;> try simp at Hsem_value₀
    case lam e₁ =>
    cases v₂ <;> try simp at Hsem_value₁
    case lam e₂ =>
    cases ε <;> simp only [log_equiv_value] at Hsem_value₀ Hsem_value₁ <;> try contradiction
    have ⟨Hτ₀, Hτ₁, Hsem_expr₀⟩ := Hsem_value₀
    have ⟨Hτ₁, Hτ₂, _⟩ := Hsem_value₁
    simp only [log_equiv_value]
    constructor; apply Hτ₀
    constructor; apply Hτ₂
    intros argv₀ argv₁ Hsem_value_arg₀
    have ⟨HvalueArg₀, HvalueArg₁⟩ := log_equiv_value.syntactic.value _ _ _ Hsem_value_arg₀
    have ⟨HτArg₀, HτArg₁⟩ := log_equiv_value.syntactic.typing _ _ _ Hsem_value_arg₀
    apply log_equiv_expr.trans; apply Hsem_expr₀
    apply Hsem_value_arg₀
    have ⟨_, _, Hsem_expr₁⟩ := Hsem_value₁
    apply Hsem_expr₁
    apply log_equiv_value.refl
    apply HvalueArg₁; apply HτArg₁
  | .fragment _ => by simp
  | .rep _ => by simp

lemma log_equiv_expr.trans :
  ∀ e₀ e₁ e₂ τ,
    log_equiv_expr e₀ e₁ τ →
    log_equiv_expr e₁ e₂ τ →
    log_equiv_expr e₀ e₂ τ :=
  by
  intros e₀ e₁ e₂ τ Hsem_expr₀ Hsem_expr₁
  simp only [log_equiv_expr] at Hsem_expr₀ Hsem_expr₁
  have ⟨v₀, v₁, Hstep₀, Hstep₁, Hsem_value₀⟩ := Hsem_expr₀
  have ⟨Hvalue₀, Hvalue₁⟩ := log_equiv_value.syntactic.value _ _ _ Hsem_value₀
  have ⟨v₂, v₃, Hstep₂, Hstep₃, Hsem_value₁⟩ := Hsem_expr₁
  have ⟨Hvalue₂, Hvalue₃⟩ := log_equiv_value.syntactic.value _ _ _ Hsem_value₁
  simp only [log_equiv_expr]
  rw [← stepn.unique_normal_forms _ _ _ Hstep₁ Hstep₂ Hvalue₁ Hvalue₂] at Hsem_value₁
  exists v₀, v₃
  constructor; apply Hstep₀
  constructor; apply Hstep₃
  apply log_equiv_value.trans
  apply Hsem_value₀; apply Hsem_value₁
end

-- Γ ⊧ e₀ ≃𝑙𝑜𝑔 e₁ : τ
-- Γ ⊧ e₁ ≃𝑙𝑜𝑔 e₂ : τ
-- ——————————————————
-- Γ ⊧ e₀ ≃𝑙𝑜𝑔 e₂ : τ
theorem log_equiv.trans :
  ∀ Γ e₀ e₁ e₂ τ,
    log_equiv Γ e₀ e₁ τ →
    log_equiv Γ e₁ e₂ τ →
    log_equiv Γ e₀ e₂ τ :=
  by
  intros Γ e₀ e₁ e₂ τ H₀ H₁
  have ⟨Hτ₀, Hτ₁, H₀⟩ := H₀
  have ⟨Hτ₁, Hτ₂, H₁⟩ := H₁
  constructor; apply Hτ₀
  constructor; apply Hτ₂
  intros γ₀ γ₁ HsemΓ
  have ⟨HτΓ₀, HτΓ₁⟩ := log_equiv_env.syntactic.typing _ _ _ HsemΓ
  apply log_equiv_expr.trans
  apply H₀; apply HsemΓ
  apply H₁; apply log_equiv_env.refl; apply HτΓ₁
