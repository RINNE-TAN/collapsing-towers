
import CollapsingTowers.TwoLevelBasic.Erasure
mutual
-- 𝓥⟦nat⟧ ≜ {(n, n) | n ∈ ℕ}
-- 𝓥⟦τ𝕒 → τ𝕓⟧ ≜ {(λ.e₀, λ.e₁) | ∀ (v₀, v₁) ∈ 𝓥⟦τ𝕒⟧. wf (λ.e₀) ∧ wf (λ.e₁) ∧ (e₀⟦0 ↦ v₀⟧, e₁⟦0 ↦ v₁⟧) ∈ 𝓔⟦τ𝕓⟧}
@[simp]
def sem_equiv_value : Expr → Expr → Ty → Prop
  | .lit n₀, .lit n₁, .nat => n₀ = n₁
  | .lam e₀, .lam e₁, (.arrow τ𝕒 τ𝕓 .pure) =>
      wf (.lam e₀) ∧
      wf (.lam e₁) ∧
      ∀ v₀ v₁,
        sem_equiv_value v₀ v₁ τ𝕒 →
        sem_equiv_expr (open_subst v₀ e₀) (open_subst v₁ e₁) τ𝕓
  | _, _, _ => false

-- 𝓔⟦τ⟧ ≜ {(e₀, e₁) | ∃v₀ v₁. e₀ ↦* v₀ ∧ e₁ ↦* v₁ ∧ (v₀, v₁) ∈ 𝓥⟦τ⟧}
@[simp]
def sem_equiv_expr (e₀ : Expr) (e₁ : Expr) (τ : Ty) : Prop :=
    ∃ v₀ v₁,
      pure_stepn e₀ v₀ ∧
      pure_stepn e₁ v₁ ∧
      sem_equiv_value v₀ v₁ τ
end

inductive sem_equiv_env : Subst → Subst → TEnv → Prop where
  | nil : sem_equiv_env [] [] []
  | cons :
    ∀ v₀ γ₀ v₁ γ₁ τ Γ,
      sem_equiv_value v₀ v₁ τ →
      sem_equiv_env γ₀ γ₁ Γ →
      sem_equiv_env (v₀ :: γ₀) (v₁ :: γ₁) ((τ, .stat) :: Γ)

-- Γ ⊧ e₀ ≈ e₁ : τ ≜ ∀ (γ₀, γ₁) ∈ 𝓖⟦Γ⟧. (γ₀(e₀), γ₁(e₁)) ∈ 𝓔⟦τ⟧
@[simp]
def sem_equiv_typing (Γ : TEnv) (e₀ : Expr) (e₁ : Expr) (τ : Ty) : Prop :=
  wf_at e₀ Γ.length ∧
  wf_at e₁ Γ.length ∧
  ∀ γ₀ γ₁,
    sem_equiv_env γ₀ γ₁ Γ →
    sem_equiv_expr (multi_subst γ₀ e₀) (multi_subst γ₁ e₁) τ

theorem sem_equiv_value_impl_value :
  ∀ v₀ v₁ τ,
    sem_equiv_value v₀ v₁ τ →
    value v₀ ∧
    value v₁ :=
  by
  intros v₀ v₁ τ Hsem_value
  cases τ
  case nat =>
    cases v₀ <;> cases v₁ <;> simp at Hsem_value
    constructor
    apply value.lit
    apply value.lit
  case arrow φ =>
    cases v₀ <;> cases v₁ <;> cases φ <;> simp at Hsem_value
    have ⟨Hwf₀, Hwf₁, _⟩ := Hsem_value
    constructor
    apply value.lam; apply Hwf₀.left
    apply value.lam; apply Hwf₁.left
  all_goals simp at Hsem_value

theorem sem_equiv_value_impl_wf :
  ∀ v₀ v₁ τ,
    sem_equiv_value v₀ v₁ τ →
    wf v₀ ∧
    wf v₁ :=
  by
  intros v₀ v₁ τ Hsem_value
  cases τ
  case nat =>
    cases v₀ <;> cases v₁ <;> simp at Hsem_value
    repeat constructor
  case arrow φ =>
    cases v₀ <;> cases v₁ <;> cases φ <;> simp at Hsem_value
    have ⟨Hwf₀, Hwf₁, _⟩ := Hsem_value
    constructor
    apply Hwf₀; apply Hwf₁
  all_goals simp at Hsem_value

theorem sem_equiv_env_impl_multi_wf :
  ∀ γ₀ γ₁ Γ,
    sem_equiv_env γ₀ γ₁ Γ →
    multi_wf γ₀ ∧
    multi_wf γ₁ :=
  by
  intros γ₀ γ₁ Γ H
  induction H
  case nil => repeat constructor
  case cons Hsem_value _ IH =>
    constructor
    . constructor; apply And.left
      apply sem_equiv_value_impl_wf
      apply Hsem_value; apply IH.left
    . constructor; apply And.right
      apply sem_equiv_value_impl_wf
      apply Hsem_value; apply IH.right

theorem sem_equiv_env_impl_length_eq :
  ∀ γ₀ γ₁ Γ,
    sem_equiv_env γ₀ γ₁ Γ →
    γ₀.length = Γ.length ∧
    γ₁.length = Γ.length :=
  by
  intros γ₀ γ₁ Γ H
  induction H
  case nil => simp
  case cons IH =>
    constructor
    . simp; apply IH.left
    . simp; apply IH.right

theorem sem_equiv_value_arrow_iff_lam :
  ∀ f₀ f₁ τ𝕒 τ𝕓,
    sem_equiv_value f₀ f₁ (.arrow τ𝕒 τ𝕓 .pure) →
    ∃ e₀ e₁,
      f₀ = .lam e₀ ∧ f₁ = .lam e₁ :=
  by
  intros f₀ f₁ τ𝕒 τ𝕓 Hsem_value
  cases f₀ <;> cases f₁ <;> simp at Hsem_value
  simp

theorem sem_equiv_env_impl_sem_equiv_value :
  ∀ γ₀ γ₁ Γ x τ,
    sem_equiv_env γ₀ γ₁ Γ →
    binds x (τ, .stat) Γ →
    sem_equiv_value (multi_subst γ₀ (.fvar x)) (multi_subst γ₁ (.fvar x)) τ :=
  by
  intros γ₀ γ₁ Γ x τ HsemΓ Hbinds
  induction HsemΓ
  case nil => nomatch Hbinds
  case cons v₀ γ₀ v₁ γ₁ τ Γ Hsem_value HsemΓ IH =>
    have ⟨Hwf₀, Hwf₁⟩ := sem_equiv_value_impl_wf _ _ _ Hsem_value
    have ⟨HEq₀, HEq₁⟩ := sem_equiv_env_impl_length_eq _ _ _ HsemΓ
    simp [HEq₀, HEq₁]
    by_cases HEqx : Γ.length = x
    . simp [if_pos HEqx]
      simp [if_pos HEqx] at Hbinds
      rw [← Hbinds, multi_subst_closed_id, multi_subst_closed_id]
      apply Hsem_value; apply Hwf₁.right; apply Hwf₀.right
    . simp [if_neg HEqx]
      simp [if_neg HEqx] at Hbinds
      apply IH; apply Hbinds
