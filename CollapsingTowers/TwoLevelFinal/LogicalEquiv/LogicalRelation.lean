import CollapsingTowers.TwoLevelFinal.SyntacticSoundness.Defs
import CollapsingTowers.TwoLevelFinal.LogicalEquiv.World

-- (σ₀, σ₁) : 𝓦 ≜ ∀ 𝓦(l₀, l₁). σ₀(l₁) = σ₀(l₁)
@[simp]
def log_well_store (𝓦 : World) (σ₀ σ₁ : Store) : Prop :=
  PartialBijection 𝓦 ∧ (
  ∀ l₀ l₁,
    𝓦 l₀ l₁ →
    ∃ n,
      binds l₀ (.lit n) σ₀ ∧
      binds l₁ (.lit n) σ₁
  )

abbrev KripkeWorld := Nat × World

@[simp]
def KripkeWorld.future : KripkeWorld → KripkeWorld → Prop
  | (k, 𝓦₀), (j, 𝓦₁) => j ≤ k ∧ 𝓦₁ ⊒ 𝓦₀

notation:max 𝓦₁ " ⊇ " 𝓦₀  => KripkeWorld.future 𝓦₀ 𝓦₁

mutual
@[simp]
def log_approx_value : KripkeWorld → Expr → Expr → Ty → Prop
  --
  --
  -- 𝓥⟦ℕ⟧ ≜ {(k, 𝓦, n, n) | n ∈ ℕ}
  | _, .lit n₀, .lit n₁, .nat => n₀ = n₁
  --
  --
  -- 𝓥⟦τ𝕒 → τ𝕓⟧ ≜ {
  --   (k, 𝓦₀, λx.e₀, λx.e₁) |
  --   ∀ (j, 𝓦₁) ⊇ (k, 𝓦₀), (j, 𝓦₁, v₀, v₁) ∈ 𝓥⟦τ𝕒⟧. (j, 𝓦₁, λx.e₀ @ v₀, λx.e₁ @ v₁) ∈ 𝓔⟦τ𝕓⟧
  -- }
  | (k, 𝓦₀), .lam e₀, .lam e₁, (.arrow τ𝕒 τ𝕓 ⊥) =>
    wf (.lam e₀) ∧ grounded (.lam e₀) ∧
    wf (.lam e₁) ∧ grounded (.lam e₁) ∧
    ∀ j 𝓦₁ v₀ v₁,
      ((j, 𝓦₁) ⊇ (k, 𝓦₀)) →
      log_approx_value (j, 𝓦₁) v₀ v₁ τ𝕒 →
      log_approx_expr (j, 𝓦₁) (.app₁ (.lam e₀) v₀) (.app₁ (.lam e₁) v₁) τ𝕓
  --
  --
  -- 𝓥⟦unit⟧ ≜ {(k, 𝓦, (), ())}
  | _, .unit, .unit, .unit => true
  --
  --
  -- 𝓥⟦ref ℕ⟧ ≜ {(k, 𝓦, l₀, l₁) | 𝓦(l₀, l₁)}
  | (_, 𝓦), .loc l₀, .loc l₁, .ref .nat => 𝓦 l₀ l₁
  | _, _, _, _ => false

-- 𝓔⟦τ⟧ ≜ {
--   (k, 𝓦₀, e₀, e₁) |
--   ∀ j ≤ k, (σ₀, σ₁) : 𝓦₀, σ₂, v₀.
--   ⟨σ₀, e₀⟩ ⇝ⱼ ⟨σ₂, v₀⟩ →
--   ∃ 𝓦₁, σ₃, v₁.
--     (k - j, 𝓦₁) ⊇ (k, 𝓦₀) ∧
--     ⟨σ₁, e₁⟩ ⇝* ⟨σ₃, v₁⟩ ∧
--     (σ₂, σ₃) : 𝓦₁ ∧
--     (k - j, 𝓦₁, v₀, v₁) ∈ 𝓥⟦τ⟧
-- }
@[simp]
def log_approx_expr : KripkeWorld → Expr → Expr → Ty → Prop
  | (k, 𝓦₀), e₀, e₁, τ =>
    ∀ j, j < k →
    ∀ σ₀ σ₁, log_well_store 𝓦₀ σ₀ σ₁ →
    ∀ σ₂ v₀, value v₀ → (⟨σ₀, e₀⟩ ⇝ ⟦j⟧ ⟨σ₂, v₀⟩) →
    ∃ 𝓦₁ σ₃ v₁,
      ((k - j, 𝓦₁) ⊇ (k, 𝓦₀)) ∧
      (⟨σ₁, e₁⟩ ⇝* ⟨σ₃, v₁⟩) ∧
      log_well_store 𝓦₁ σ₂ σ₃ ∧
      log_approx_value (k - j, 𝓦₁) v₀ v₁ τ
end
