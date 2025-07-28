import CollapsingTowers.TwoLvLBasic.SyntacticTyping.Defs

mutual
-- 𝓥⟦ℕ⟧ ≜ {(n, n) | n ∈ ℕ}
-- 𝓥⟦τ𝕒 → τ𝕓⟧ ≜ {(λ.e₀, λ.e₁) | ∀ (v₀, v₁) ∈ 𝓥⟦τ𝕒⟧. (e₀⟦0 ↦ v₀⟧, e₁⟦0 ↦ v₁⟧) ∈ 𝓔⟦τ𝕓⟧}
@[simp]
def logic_equiv_value : Expr → Expr → Ty → Prop
  | .lit n₀, .lit n₁, .nat => n₀ = n₁
  | .lam e₀, .lam e₁, (.arrow τ𝕒 τ𝕓 .pure) =>
      wf (.lam e₀) ∧
      wf (.lam e₁) ∧
      ∀ v₀ v₁,
        logic_equiv_value v₀ v₁ τ𝕒 →
        logic_equiv_expr (opening 0 v₀ e₀) (opening 0 v₁ e₁) τ𝕓
  | _, _, _ => false

-- 𝓔⟦τ⟧ ≜ {(e₀, e₁) | ∃v₀ v₁. e₀ ⇾* v₀ ∧ e₁ ⇾* v₁ ∧ (v₀, v₁) ∈ 𝓥⟦τ⟧}
@[simp]
def logic_equiv_expr (e₀ : Expr) (e₁ : Expr) (τ : Ty) : Prop :=
    ∃ v₀ v₁,
      (e₀ ⇾* v₀) ∧
      (e₁ ⇾* v₁) ∧
      logic_equiv_value v₀ v₁ τ
end

inductive logic_equiv_env : Subst → Subst → TEnv → Prop where
  | nil : logic_equiv_env [] [] []
  | cons :
    ∀ v₀ γ₀ v₁ γ₁ τ Γ,
      logic_equiv_value v₀ v₁ τ →
      logic_equiv_env γ₀ γ₁ Γ →
      logic_equiv_env (v₀ :: γ₀) (v₁ :: γ₁) ((τ, 𝟙) :: Γ)

-- Γ ⊧ e₀ ≈ e₁ : τ ≜ ∀ (γ₀, γ₁) ∈ 𝓖⟦Γ⟧. (γ₀(e₀), γ₁(e₁)) ∈ 𝓔⟦τ⟧
@[simp]
def logic_equiv_typing (Γ : TEnv) (e₀ : Expr) (e₁ : Expr) (τ : Ty) : Prop :=
  wf_at e₀ Γ.length ∧
  wf_at e₁ Γ.length ∧
  ∀ γ₀ γ₁,
    logic_equiv_env γ₀ γ₁ Γ →
    logic_equiv_expr (multi_subst γ₀ e₀) (multi_subst γ₁ e₁) τ

lemma logic_equiv_value_impl_syntactic_value :
  ∀ v₀ v₁ τ,
    logic_equiv_value v₀ v₁ τ →
    value v₀ ∧ value v₁ :=
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
