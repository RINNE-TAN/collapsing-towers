import CollapsingTowers.TwoLevelBasic.CtxEquiv.Defs
import CollapsingTowers.TwoLevelBasic.LogicalEquiv.Fundamental

-- Γ ⊧ e₀ ≈𝑐𝑖𝑢 e₁ : τ ≜
--   Γ ⊢ e₀ : τ ∧
--   Γ ⊢ e₁ : τ ∧
--   ∀ (⦰ ⊢ γ : Γ, ⦰ ⊢ E⟦⦰ ⊢ τ⟧ : ℕ).
--   ∀ v. E⟦γ(e₀)⟧ ⇝* v ↔ E⟦γ(e₁)⟧ ⇝* v
@[simp]
def ciu_equiv (Γ : TEnv) (e₀ e₁: Expr) (τ : Ty) : Prop :=
  typing Γ 𝟚 e₀ τ ⊥ ∧
  typing Γ 𝟚 e₁ τ ⊥ ∧
    ∀ γ, typing.subst γ Γ →
    ∀ E,
      ctx𝔼 E →
      ObsCtxℂ ⦰ τ E ⦰ .nat →
      ∀ v, value v → (
        (E⟦msubst γ e₀⟧ ⇝* v) ↔ (E⟦msubst γ e₁⟧ ⇝* v)
      )

-- Γ ⊧ e₀ ≈𝑐𝑡𝑥 e₁ : τ
-- ——————————————————
-- Γ ⊧ e₀ ≈𝑐𝑖𝑢 e₁ : τ
theorem ctx_equiv_impl_ciu_equiv :
  ∀ Γ τ e₀ e₁,
    ctx_equiv Γ e₀ e₁ τ →
    ciu_equiv Γ e₀ e₁ τ :=
  by
  intros Γ τ e₀ e₁ Hctx
  constructor; apply Hctx.left
  constructor; apply Hctx.right.left
  intros γ Hγ
  induction Hγ generalizing e₀ e₁
  case nil =>
    intros E HE
    apply Hctx.right.right
  case cons v γ τ𝕧 Γ Hvalue Hτv Hτγ IH =>
    intros E HE HCE
    admit
