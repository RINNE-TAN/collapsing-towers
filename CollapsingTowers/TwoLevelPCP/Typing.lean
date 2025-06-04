
import CollapsingTowers.TwoLevelPCP.Syntax
import CollapsingTowers.TwoLevelPCP.SmallStep
import CollapsingTowers.TwoLevelPCP.Env
inductive typing : TEnv → Stage → Expr → Ty → Prop where
  | fvar : ∀ Γ 𝕊 x τ,
    binds x τ 𝕊 Γ →
    typing Γ 𝕊 (.fvar x) τ
  | lam₁ : ∀ Γ 𝕊 e τ𝕒 τ𝕓,
    typing ((τ𝕒, 𝕊) :: Γ) 𝕊 (open₀ Γ.length e) τ𝕓 →
    well_binding_time 𝕊 τ𝕒 →
    closed_at e Γ.length →
    typing Γ 𝕊 (.lam₁ e) (.arrow τ𝕒 τ𝕓)
  | lift_lam : ∀ Γ e τ𝕒 τ𝕓,
    typing Γ .stat e (.arrow (.fragment τ𝕒) (.fragment τ𝕓)) →
    typing Γ .stat (.lift e) (.fragment (.arrow τ𝕒 τ𝕓))
  | app₁ : ∀ Γ 𝕊 f arg τ𝕒 τ𝕓,
    typing Γ 𝕊 f (.arrow τ𝕒 τ𝕓) →
    typing Γ 𝕊 arg τ𝕒 →
    typing Γ 𝕊 (.app₁ f arg) τ𝕓
  | app₂ : ∀ Γ f arg τ𝕒 τ𝕓,
    typing Γ .stat f (.fragment (.arrow τ𝕒 τ𝕓)) →
    typing Γ .stat arg (.fragment τ𝕒) →
    typing Γ .stat (.app₂ f arg) (.fragment τ𝕓)
  | plus₁ : ∀ Γ 𝕊 l r,
    typing Γ 𝕊 l .nat →
    typing Γ 𝕊 r .nat →
    typing Γ 𝕊 (.plus₁ l r) .nat
  | plus₂ : ∀ Γ l r,
    typing Γ .stat l (.fragment .nat) →
    typing Γ .stat r (.fragment .nat) →
    typing Γ .stat (.plus₂ l r) (.fragment .nat)
  | lit₁ : ∀ Γ 𝕊 n,
    typing Γ 𝕊 (.lit₁ n) .nat
  | lift_lit : ∀ Γ n,
    typing Γ .stat n .nat →
    typing Γ .stat (.lift n) (.fragment .nat)
  | code₁ : ∀ Γ x τ,
    binds x τ .dyn Γ →
    typing Γ .stat (.code (.fvar x)) (.fragment τ)
  | code₂ : ∀ Γ e τ,
    typing Γ .dyn e τ →
    typing Γ .stat (.code e) (.rep τ)
  | lift_code : ∀ Γ e τ,
    typing Γ .stat e (.fragment τ) →
    typing Γ .stat e (.rep τ)
  | reflect : ∀ Γ e τ,
    typing Γ .dyn e τ →
    typing Γ .stat (.reflect e) (.fragment τ)
  | lam𝕔 : ∀ Γ e τ𝕒 τ𝕓,
    typing ((τ𝕒, .dyn) :: Γ) .stat (open₀ Γ.length e) (.rep τ𝕓) →
    well_binding_time .dyn τ𝕒 →
    closed_at e Γ.length →
    typing Γ .stat (.lam𝕔 e) (.fragment (.arrow τ𝕒 τ𝕓))
  | lets : ∀ Γ 𝕊 b e τ𝕒 τ𝕓,
    typing Γ 𝕊 b τ𝕒 →
    typing ((τ𝕒, 𝕊) :: Γ) 𝕊 (open₀ Γ.length e) τ𝕓 →
    well_binding_time 𝕊 τ𝕒 →
    closed_at e Γ.length →
    typing Γ 𝕊 (.lets b e) τ𝕓
  | let𝕔 : ∀ Γ b e τ𝕒 τ𝕓,
    typing Γ .dyn b τ𝕒 →
    typing ((τ𝕒, .dyn) :: Γ) .stat (open₀ Γ.length e) (.rep τ𝕓) →
    well_binding_time .dyn τ𝕒 →
    closed_at e Γ.length →
    typing Γ .stat (.let𝕔 b e) (.rep τ𝕓)
