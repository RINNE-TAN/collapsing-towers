import CollapsingTowers.TwoLevelRec.SyntacticTyping.Defs

mutual
-- 𝓥⟦ℕ⟧ₖ ≜ {(n, n) | n ∈ ℕ}
-- 𝓥⟦τ𝕒 → τ𝕓⟧ₖ ≜ {(λ.e₀, λ.e₁) | ∀ j < k, (v₀, v₁) ∈ 𝓥⟦τ𝕒⟧ⱼ. (λ.e₀ @ v₀, λ.e₁ @ v₁) ∈ 𝓔⟦τ𝕓⟧ⱼ}
@[simp]
def logic_rel_value : ℕ → Expr → Expr → Ty → Prop
  | _, .lit n₀, .lit n₁, .nat => n₀ = n₁
  | k, .lam e₀, .lam e₁, (.arrow τ𝕒 τ𝕓 .pure) =>
    ∀ j, j < k →
      wf (.lam e₀) ∧
      wf (.lam e₁) ∧
      ∀ v₀ v₁,
        logic_rel_value j v₀ v₁ τ𝕒 →
        logic_rel_expr j (.app₁ (.lam e₀) v₀) (.app₁ (.lam e₁) v₁) τ𝕓
  | _, _, _, _ => false
termination_by k _ _ _ => k * 2
decreasing_by all_goals omega

-- 𝓔⟦τ⟧ₖ ≜ {(e₀, e₁) | ∀ j < k, v₀. e₀ ⇾ⱼ v₀ → ∃ v₁, e₁ ⇾* v₁ ∧ (v₀, v₁) ∈ 𝓥⟦τ⟧ₖ₋ⱼ}
@[simp]
def logic_rel_expr (k : ℕ) (e₀ : Expr) (e₁ : Expr) (τ : Ty) : Prop :=
    ∀ j, j < k →
      ∀ v₀, (e₀ ⇾ ⟦j⟧ v₀) → value v₀ →
      ∃ v₁, (e₁ ⇾* v₁) ∧
        logic_rel_value (k - j) v₀ v₁ τ
termination_by k * 2 + 1
decreasing_by all_goals omega
end

inductive logic_rel_env : ℕ → Subst → Subst → TEnv → Prop where
  | nil : ∀ k, logic_rel_env k [] [] []
  | cons :
    ∀ k v₀ γ₀ v₁ γ₁ τ Γ,
      logic_rel_value k v₀ v₁ τ →
      logic_rel_env k γ₀ γ₁ Γ →
      logic_rel_env k (v₀ :: γ₀) (v₁ :: γ₁) ((τ, 𝟙) :: Γ)

-- Γ ⊧ e₀ ≤𝑙𝑜𝑔 e₁ : τ ≜ ∀ k ≥ 0, (γ₀, γ₁) ∈ 𝓖⟦Γ⟧ₖ. (γ₀(e₀), γ₁(e₁)) ∈ 𝓔⟦τ⟧ₖ
@[simp]
def logic_rel_typing (Γ : TEnv) (e₀ : Expr) (e₁ : Expr) (τ : Ty) : Prop :=
  wf_at e₀ Γ.length ∧
  wf_at e₁ Γ.length ∧
  ∀ k γ₀ γ₁,
    logic_rel_env k γ₀ γ₁ Γ →
    logic_rel_expr k (multi_subst γ₀ e₀) (multi_subst γ₁ e₁) τ

-- Γ ⊧ e₀ ≈𝑙𝑜𝑔 e₁ : τ ≜ Γ ⊧ e₀ ≤𝑙𝑜𝑔 e₁ : τ ∧ Γ ⊧ e₁ ≤𝑙𝑜𝑔 e₀ : τ
@[simp]
def logic_equiv (Γ : TEnv) (e₀ : Expr) (e₁ : Expr) (τ : Ty) : Prop :=
  logic_rel_typing Γ e₀ e₁ τ ∧ logic_rel_typing Γ e₁ e₀ τ
