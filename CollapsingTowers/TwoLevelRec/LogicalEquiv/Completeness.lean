import CollapsingTowers.TwoLevelRec.CtxEquiv.Defs
import CollapsingTowers.TwoLevelRec.LogicalEquiv.LogicalRelation

-- Γ ⊢ e₀ ≤𝑐𝑖𝑢 e₁ : τ ≜
--   Γ ⊢ e₀ : τ →
--   Γ ⊢ e₁ : τ →
--   ∀ (∅ ⊢ γ : Γ, ∅ ⊢ E⟦∅ ⊢ τ⟧ : τ𝕖).
--   E⟦γ(e₀)⟧⇓ → E⟦γ(e₁)⟧⇓
@[simp]
def ciu_approx (Γ : TEnv) (e₀ e₁: Expr) (τ : Ty) : Prop :=
  typing Γ 𝟚 e₀ τ ∅ →
  typing Γ 𝟚 e₁ τ ∅ →
    ∀ γ, typing.subst γ Γ →
    ∀ E τ𝕖, ObsCtxℂ [] τ E [] τ𝕖 →
      termination E⟦multi_subst γ e₀⟧ →
      termination E⟦multi_subst γ e₁⟧

-- Γ ⊧ e₀ ≤𝑐𝑡𝑥 e₁ : τ
-- ——————————————————
-- Γ ⊢ e₀ ≤𝑐𝑖𝑢 e₁ : τ
theorem ciu_approx.completeness :
  ∀ Γ τ e₀ e₁,
    ctx_approx Γ e₀ e₁ τ →
    ciu_approx Γ e₀ e₁ τ :=
  by
  intros Γ τ e₀ e₁ Hctx Hτ₀ Hτ₁ γ Hτγ
  admit
