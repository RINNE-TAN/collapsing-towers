
import CollapsingTowers.TwoLevelPCP.Syntax
import CollapsingTowers.TwoLevelPCP.SmallStep
import CollapsingTowers.TwoLevelPCP.Env
inductive typing : Stage → TEnv → Expr → Ty → Prop where
  | fvar : ∀ 𝕊 Γ x τ, binds x τ 𝕊 Γ -> typing 𝕊 Γ (.fvar x) τ
  | lam₁ : ∀ 𝕊 Γ e τ𝕒 τ𝕓,
    typing 𝕊 ((τ𝕒, 𝕊) :: Γ) (open₀ Γ.length e) τ𝕓 ->
    closed_at e Γ.length ->
    typing 𝕊 Γ (.lam₁ e) (.arrow τ𝕒 τ𝕓)
