import Mathlib.Data.Nat.Basic

inductive Expr : Type where
  | bvar (i : ℕ)
  | fvar (x : ℕ)
  | lam (e : Expr)
  | app₁ (f : Expr) (arg : Expr)
  | app₂ (f : Expr) (arg : Expr)
  | lit (n : ℕ)
  | lift (e : Expr)
  | run (e : Expr)
  | code (e : Expr)
  | reflect (e : Expr)
  | lam𝕔 (e : Expr)
  | lets (b : Expr) (e : Expr)
  | lets𝕔 (b : Expr) (e : Expr)
  | unit
  | loc (l : ℕ)
  | load₁ (e : Expr)
  | alloc₁ (e : Expr)
  | store₁ (l : Expr) (r : Expr)
  | load₂ (e : Expr)
  | alloc₂ (e : Expr)
  | store₂ (l : Expr) (r : Expr)

-- log_equiv_value
--
--
-- 𝓥⟦ℕ⟧ ≜ {(𝓦, n, n) | n ∈ ℕ}
--
--
-- 𝓥⟦τ𝕒 → τ𝕓⟧ ≜ {
--   (𝓦₀, λx.e₀, λx.e₁) |
--   ∀ 𝓦₀ ⊑ 𝓦₁, (𝓦₁, v₀, v₁) ∈ 𝓥⟦τ𝕒⟧. (𝓦₁, λx.e₀ @ v₀, λx.e₁ @ v₁) ∈ 𝓔⟦τ𝕓⟧
-- }
--
--
-- 𝓥⟦ref ℕ⟧ ≜ {(𝓦, l₀, l₁) | 𝓦(l₀, l₁)}


-- log_equiv_store
--
--
-- (σ₀, σ₁) : 𝓦 ≜ ∀ 𝓦(l₀, l₁). σ₀(l₁) = σ₀(l₁)


-- log_equiv_expr
--
--
-- 𝓔⟦τ⟧ ≜ {
--   (𝓦₀, e₀, e₁) |
--   ∀ (σ₀, σ₁) : 𝓦₀.
--   ∃ σ₂, σ₃, v₀, v₁, 𝓦₁.
--   𝓦₀ ⊑ 𝓦₁ ∧
--   ⟨σ₀, e₀⟩ ⇝* ⟨σ₂, v₀⟩ ∧
--   ⟨σ₁, e₁⟩ ⇝* ⟨σ₃, v₁⟩ ∧
--   (σ₂, σ₃) : 𝓦₁ ∧
--   (𝓦₁, v₀, v₁) ∈ 𝓥⟦τ⟧
-- }


-- log_equiv_env
--
--
-- (𝓦, γ₀, γ₁) ∈ 𝓖⟦Γ⟧ ≜ ∀ x ∈ dom(Γ). (𝓦, γ₀(x), γ₁(x)) ∈ 𝓥⟦Γ(x)⟧


-- log_equiv
--
--
-- Γ ⊧ e₀ ≈𝑙𝑜𝑔 e₁ : τ ≜ ∀ 𝓦, (𝓦, γ₀, γ₁) ∈ 𝓖⟦Γ⟧. (𝓦, γ₀(e₀), γ₁(e₁)) ∈ 𝓔⟦τ⟧
