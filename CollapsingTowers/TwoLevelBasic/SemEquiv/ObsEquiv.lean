
import CollapsingTowers.TwoLevelBasic.SemEquiv.Fundamental
-- Γ ⊢ B⟦Δ ⊢ τδ⟧ : τγ ≜ ∀ (Δ ⊢ e : τδ) → Γ ⊢ B⟦e⟧ : τγ
inductive ObsCtx𝔹 :
  TEnv → -- Δ
  Ty →   -- τδ
  Ctx →  -- ℂ
  TEnv → -- Γ
  Ty →   -- τγ
  Prop where
  | lam : ∀ Γ τ𝕒 τ𝕓, ObsCtx𝔹 ((τ𝕒, .stat) :: Γ) τ𝕓 (fun X => .lam (close₀ Γ.length X)) Γ (.arrow τ𝕒 τ𝕓 ∅)
  | appl₁ : ∀ Γ arg τ𝕒 τ𝕓, typing_reification Γ arg τ𝕒 ∅ → ObsCtx𝔹 Γ (.arrow τ𝕒 τ𝕓 ∅) (fun X => .app₁ X arg) Γ τ𝕓
  | appr₁ : ∀ Γ f τ𝕒 τ𝕓, typing_reification Γ f (.arrow τ𝕒 τ𝕓 ∅) ∅ → ObsCtx𝔹 Γ τ𝕒 (fun X => .app₁ f X) Γ τ𝕓
  | letsl : ∀ Γ e τ𝕒 τ𝕓, typing_reification ((τ𝕒, .stat) :: Γ) e τ𝕓 ∅ → ObsCtx𝔹 Γ τ𝕒 (fun X => .lets X e) Γ τ𝕓
  | letsr : ∀ Γ b τ𝕒 τ𝕓, typing_reification Γ b τ𝕒 ∅ → ObsCtx𝔹 ((τ𝕒, .stat) :: Γ) τ𝕓 (fun X => .lets b (close₀ Γ.length X)) Γ τ𝕓

inductive ObsCtxℂ : TEnv → Ty → Ctx → TEnv → Ty → Prop where
  | hole : ∀ Γ τ, ObsCtxℂ Γ τ id Γ τ
  -- Γ ⊢ B⟦Δ ⊢ τδ⟧ : τγ
  -- Δ ⊢ C⟦Ψ ⊢ τψ⟧ : τδ
  -- ———————————————————————
  -- Γ ⊢ (B ∘ C)⟦Ψ ⊢ τψ⟧ : τγ
  | cons𝔹 :
    ∀ Ψ Δ Γ τψ τδ τγ C E,
      ObsCtx𝔹 Δ τδ C Γ τγ →
      ObsCtxℂ Ψ τψ E Δ τδ →
      ObsCtxℂ Ψ τψ (C ∘ E) Γ τγ

-- e₀ ≈ e₁ ≜ ∀ ([] ⊢ C⟦Γ ⊢ τ⟧ : nat). ∀ v. C⟦e₀⟧ ↦* v ↔ C⟦e₁⟧ ↦* v
@[simp]
def obs_equiv (Γ : TEnv) (e₀ : Expr) (e₁ : Expr) (τ : Ty) : Prop :=
  typing_reification Γ e₀ τ ∅ →
  typing_reification Γ e₁ τ ∅ →
  ∀ C,
    ObsCtxℂ Γ τ C [] .nat →
    ∀ v,
      stepn C⟦e₀⟧ v ↔ stepn C⟦e₁⟧ v
