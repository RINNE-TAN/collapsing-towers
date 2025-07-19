
import CollapsingTowers.TwoLevelBasic.SemEquiv.SemTyping
-- (v₀, v₁) ∈ 𝓥⟦τ⟧ → (v₁, v₀) ∈ 𝓥⟦τ⟧
-- ————————————————————————————————
-- (e₀, e₁) ∈ 𝓔⟦τ⟧ → (e₁, e₀) ∈ 𝓔⟦τ⟧
theorem value_symm_impl_expr_symm :
  ∀ τ,
    (∀ v₀ v₁, sem_equiv_value v₀ v₁ τ → sem_equiv_value v₁ v₀ τ) →
    (∀ e₀ e₁, sem_equiv_expr e₀ e₁ τ → sem_equiv_expr e₁ e₀ τ) :=
    by
    intros τ Hsem_value_symm e₀ e₁ Hsem_expr
    simp only [sem_equiv_expr] at Hsem_expr
    have ⟨v₀, v₁, Hstepv₀, Hstepv₁, Hsem_value⟩ := Hsem_expr
    simp only [sem_equiv_expr]
    exists v₁, v₀
    constructor; apply Hstepv₁
    constructor; apply Hstepv₀
    apply Hsem_value_symm; apply Hsem_value

-- (v₀, v₁) ∈ 𝓥⟦τ⟧
-- ———————————————
-- (v₁, v₀) ∈ 𝓥⟦τ⟧
theorem sem_equiv_value_symm :
  ∀ v₀ v₁ τ,
    sem_equiv_value v₀ v₁ τ →
    sem_equiv_value v₁ v₀ τ :=
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
        simp only [sem_equiv_value] at Hsem_value
        have ⟨Hwf₀, Hwf₁, Hsem_value_lam⟩ := Hsem_value
        simp only [sem_equiv_value]
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
theorem sem_equiv_expr_symm :
  ∀ e₀ e₁ τ,
    sem_equiv_expr e₀ e₁ τ →
    sem_equiv_expr e₁ e₀ τ :=
  by
  intros e₀ e₁ τ
  apply value_symm_impl_expr_symm
  intros v₀ v₁
  apply sem_equiv_value_symm

-- (γ₀, γ₁) ∈ 𝓖⟦Γ⟧
-- ———————————————
-- (γ₁, γ₀) ∈ 𝓖⟦Γ⟧
theorem sem_equiv_env_symm :
  ∀ γ₀ γ₁ Γ,
    sem_equiv_env γ₀ γ₁ Γ →
    sem_equiv_env γ₁ γ₀ Γ :=
  by
  intros γ₀ γ₁ Γ HsemΓ
  induction HsemΓ
  case nil => apply sem_equiv_env.nil
  case cons Hsem_value _ IH =>
    apply sem_equiv_env.cons
    apply sem_equiv_value_symm; apply Hsem_value
    apply IH

-- Γ ⊧ e₀ ≈ e₁ : τ
-- ———————————————
-- Γ ⊧ e₁ ≈ e₀ : τ
theorem sem_equiv_typing_symm :
  ∀ Γ e₀ e₁ τ,
    sem_equiv_typing Γ e₀ e₁ τ →
    sem_equiv_typing Γ e₁ e₀ τ :=
  by
  intros Γ e₀ e₁ τ Hsem
  rw [sem_equiv_typing] at Hsem
  rw [sem_equiv_typing]
  have ⟨Hwf₀, Hwf₁, Hsem⟩ := Hsem
  constructor; apply Hwf₁
  constructor; apply Hwf₀
  intros γ₀ γ₁ HsemΓ
  apply sem_equiv_expr_symm; apply Hsem
  apply sem_equiv_env_symm; apply HsemΓ
