import CollapsingTowers.TwoLevelBasic.LogicalEquiv.LogicalRelation

-- (v₀, v₁) ∈ 𝓥⟦τ⟧ → (v₁, v₀) ∈ 𝓥⟦τ⟧
-- ————————————————————————————————
-- (e₀, e₁) ∈ 𝓔⟦τ⟧ → (e₁, e₀) ∈ 𝓔⟦τ⟧
lemma value_symm_impl_expr_symm :
  ∀ τ,
    (∀ v₀ v₁, log_equiv_value v₀ v₁ τ → log_equiv_value v₁ v₀ τ) →
    (∀ e₀ e₁, log_equiv_expr e₀ e₁ τ → log_equiv_expr e₁ e₀ τ) :=
    by
    intros τ Hsem_value_symm e₀ e₁ Hsem_expr
    simp only [log_equiv_expr] at Hsem_expr
    have ⟨v₀, v₁, Hstepv₀, Hstepv₁, Hsem_value⟩ := Hsem_expr
    simp only [log_equiv_expr]
    exists v₁, v₀
    constructor; apply Hstepv₁
    constructor; apply Hstepv₀
    apply Hsem_value_symm; apply Hsem_value

-- (v₀, v₁) ∈ 𝓥⟦τ⟧
-- ———————————————
-- (v₁, v₀) ∈ 𝓥⟦τ⟧
lemma log_equiv_value.symm :
  ∀ v₀ v₁ τ,
    log_equiv_value v₀ v₁ τ →
    log_equiv_value v₁ v₀ τ :=
    by
    intros v₀ v₁ τ Hsem_value
    induction τ generalizing v₀ v₁
    case nat =>
      cases v₀ <;> cases v₁ <;> simp at *
      omega
    case arrow τ𝕒 τ𝕓 φ IH𝕒 IH𝕓 =>
      cases v₀ <;> try simp at Hsem_value
      case lam e₀ =>
      cases v₁ <;> try simp at Hsem_value
      case lam e₁ =>
      cases φ
      case reify => simp at Hsem_value
      case pure =>
        simp only [log_equiv_value] at Hsem_value
        have ⟨Hwf₀, Hwf₁, Hsem_value_lam⟩ := Hsem_value
        simp only [log_equiv_value]
        constructor; apply Hwf₁
        constructor; apply Hwf₀
        intros v₀ v₁ Hsem_value
        apply value_symm_impl_expr_symm; apply IH𝕓
        apply Hsem_value_lam; apply IH𝕒
        apply Hsem_value
    case fragment => simp at Hsem_value
    case rep => simp at Hsem_value

-- (e₀, e₁) ∈ 𝓔⟦τ⟧
-- ———————————————
-- (e₁, e₀) ∈ 𝓔⟦τ⟧
lemma log_equiv_expr.symm :
  ∀ e₀ e₁ τ,
    log_equiv_expr e₀ e₁ τ →
    log_equiv_expr e₁ e₀ τ :=
  by
  intros e₀ e₁ τ
  apply value_symm_impl_expr_symm
  intros v₀ v₁
  apply log_equiv_value.symm

-- (γ₀, γ₁) ∈ 𝓖⟦Γ⟧
-- ———————————————
-- (γ₁, γ₀) ∈ 𝓖⟦Γ⟧
lemma log_equiv_env.symm :
  ∀ γ₀ γ₁ Γ,
    log_equiv_env γ₀ γ₁ Γ →
    log_equiv_env γ₁ γ₀ Γ :=
  by
  intros γ₀ γ₁ Γ HsemΓ
  induction HsemΓ
  case nil => apply log_equiv_env.nil
  case cons Hsem_value _ IH =>
    apply log_equiv_env.cons
    apply log_equiv_value.symm; apply Hsem_value
    apply IH

-- Γ ⊧ e₀ ≈ e₁ : τ
-- ———————————————
-- Γ ⊧ e₁ ≈ e₀ : τ
theorem log_equiv_typing.symm :
  ∀ Γ e₀ e₁ τ,
    log_equiv_typing Γ e₀ e₁ τ →
    log_equiv_typing Γ e₁ e₀ τ :=
  by
  intros Γ e₀ e₁ τ Hsem
  rw [log_equiv_typing] at Hsem
  rw [log_equiv_typing]
  have ⟨Hwf₀, Hwf₁, Hsem⟩ := Hsem
  constructor; apply Hwf₁
  constructor; apply Hwf₀
  intros γ₀ γ₁ HsemΓ
  apply log_equiv_expr.symm; apply Hsem
  apply log_equiv_env.symm; apply HsemΓ
