
import CollapsingTowers.TwoLevelBasic.SemEquiv.SemTyping
import CollapsingTowers.TwoLevelBasic.SemEquiv.Symmetry
import CollapsingTowers.TwoLevelBasic.Deterministic
-- (v₀, v₁) ∈ 𝓥⟦τ⟧ → (v₁, v₂) ∈ 𝓥⟦τ⟧ → (v₀, v₂) ∈ 𝓥⟦τ⟧
-- ———————————————————————————————————————————————————
-- (e₀, e₁) ∈ 𝓔⟦τ⟧ → (e₁, e₂) ∈ 𝓔⟦τ⟧ → (e₀, e₂) ∈ 𝓔⟦τ⟧
theorem value_trans_impl_expr_trans :
  ∀ τ,
    (∀ v₀ v₁ v₂,
      sem_equiv_value v₀ v₁ τ →
      sem_equiv_value v₁ v₂ τ →
      sem_equiv_value v₀ v₂ τ) →
    (∀ e₀ e₁ e₂,
      sem_equiv_expr e₀ e₁ τ →
      sem_equiv_expr e₁ e₂ τ →
      sem_equiv_expr e₀ e₂ τ) :=
  by
  intros τ Hsem_value_trans e₀ e₁ e₂ Hsem_expr₀ Hsem_expr₁
  simp only [sem_equiv_expr] at Hsem_expr₀ Hsem_expr₁
  have ⟨v₀, v₁, Hstepv₀, Hstepv₁, Hsem_value₀⟩ := Hsem_expr₀
  have ⟨Hvalue₀, Hvalue₁⟩ := sem_equiv_value_impl_value _ _ _ Hsem_value₀
  have ⟨v₂, v₃, Hstepv₂, Hstepv₃, Hsem_value₁⟩ := Hsem_expr₁
  have ⟨Hvalue₂, Hvalue₃⟩ := sem_equiv_value_impl_value _ _ _ Hsem_value₁
  have Hstepv₁ := pure_stepn_impl_stepn _ _ Hstepv₁
  have Hstepv₂ := pure_stepn_impl_stepn _ _ Hstepv₂
  rw [← church_rosser _ _ _ Hstepv₁ Hstepv₂ Hvalue₁ Hvalue₂] at Hsem_value₁
  simp only [sem_equiv_expr]
  exists v₀, v₃
  constructor; apply Hstepv₀
  constructor; apply Hstepv₃
  apply Hsem_value_trans
  apply Hsem_value₀; apply Hsem_value₁

-- (v₀, v₁) ∈ 𝓥⟦τ⟧
-- (v₁, v₂) ∈ 𝓥⟦τ⟧
-- ———————————————
-- (v₀, v₂) ∈ 𝓥⟦τ⟧
theorem sem_equiv_value_trans :
  ∀ v₀ v₁ v₂ τ,
    sem_equiv_value v₀ v₁ τ →
    sem_equiv_value v₁ v₂ τ →
    sem_equiv_value v₀ v₂ τ :=
  by
  intros v₀ v₁ v₂ τ Hsem_value₀ Hsem_value₁
  induction τ generalizing v₀ v₁ v₂
  case nat =>
    cases v₀ <;> cases v₁ <;> cases v₂ <;> simp at *
    omega
  case arrow τ𝕒 τ𝕓 φ IH𝕒 IH𝕓 =>
    cases v₀ <;> try simp at Hsem_value₀
    case lam e₀ =>
    cases v₁ <;> try simp at Hsem_value₀
    case lam e₁ =>
    cases v₂ <;> try simp at Hsem_value₁
    case lam e₂ =>
    cases φ
    case pure =>
      simp only [sem_equiv_value] at Hsem_value₀ Hsem_value₁
      have ⟨Hwf₀, Hwf₁, Hsem_value_lam₀⟩ := Hsem_value₀
      have ⟨Hwf₁, Hwf₂, Hsem_value_lam₁⟩ := Hsem_value₁
      simp only [sem_equiv_value]
      constructor; apply Hwf₀
      constructor; apply Hwf₂
      intros v₀ v₁ Hsem_value
      apply value_trans_impl_expr_trans; apply IH𝕓
      apply Hsem_value_lam₀; apply Hsem_value
      apply Hsem_value_lam₁; apply IH𝕒
      apply sem_equiv_value_symm; apply Hsem_value; apply Hsem_value
    case reify => simp at Hsem_value₀
  case fragment => simp at Hsem_value₀
  case rep => simp at Hsem_value₀

-- (e₀, e₁) ∈ 𝓔⟦τ⟧
-- (e₁, e₂) ∈ 𝓔⟦τ⟧
-- ———————————————
-- (e₀, e₂) ∈ 𝓔⟦τ⟧
theorem sem_equiv_expr_trans :
  ∀ e₀ e₁ e₂ τ,
    sem_equiv_expr e₀ e₁ τ →
    sem_equiv_expr e₁ e₂ τ →
    sem_equiv_expr e₀ e₂ τ :=
  by
  intros e₀ e₁ e₂ τ
  apply value_trans_impl_expr_trans
  intros v₀ v₁ v₂
  apply sem_equiv_value_trans

-- (γ₀, γ₁) ∈ 𝓖⟦Γ⟧
-- (γ₁, γ₂) ∈ 𝓖⟦Γ⟧
-- ———————————————
-- (γ₀, γ₂) ∈ 𝓖⟦Γ⟧
theorem sem_equiv_env_trans :
  ∀ γ₀ γ₁ γ₂ Γ,
    sem_equiv_env γ₀ γ₁ Γ →
    sem_equiv_env γ₁ γ₂ Γ →
    sem_equiv_env γ₀ γ₂ Γ :=
  by
  intros γ₀ γ₁ γ₂ Γ HsemΓ₀ HsemΓ₁
  induction HsemΓ₀ generalizing γ₂
  case nil =>
    cases HsemΓ₁
    apply sem_equiv_env.nil
  case cons Hsem_value₀ _ IH =>
    cases HsemΓ₁
    case cons Hsem_value₁ _ =>
    apply sem_equiv_env.cons
    apply sem_equiv_value_trans
    apply Hsem_value₀; apply Hsem_value₁
    apply IH; assumption

-- Γ ⊧ e₀ ≈ e₁ : τ
-- Γ ⊧ e₁ ≈ e₂ : τ
-- ———————————————
-- Γ ⊧ e₀ ≈ e₂ : τ
theorem sem_equiv_typing_trans :
  ∀ Γ e₀ e₁ e₂ τ,
    sem_equiv_typing Γ e₀ e₁ τ →
    sem_equiv_typing Γ e₁ e₂ τ →
    sem_equiv_typing Γ e₀ e₂ τ :=
  by
  intros Γ e₀ e₁ e₂ τ Hsem₀ Hsem₁
  rw [sem_equiv_typing] at Hsem₀ Hsem₁
  rw [sem_equiv_typing]
  have ⟨Hwf₀, Hwf₁, Hsem₀⟩ := Hsem₀
  have ⟨Hwf₁, Hwf₂, Hsem₁⟩ := Hsem₁
  constructor; apply Hwf₀
  constructor; apply Hwf₂
  intros γ₀ γ₁ HsemΓ
  apply sem_equiv_expr_trans
  apply Hsem₀; apply HsemΓ
  apply Hsem₁; apply sem_equiv_env_trans
  apply sem_equiv_env_symm; apply HsemΓ; apply HsemΓ
