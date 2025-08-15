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
    ∀ E τ𝕖,
      ctx𝔼 E →
      ObsCtxℂ [] τ E [] τ𝕖 →
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
  induction Hτγ generalizing e₀ e₁
  case nil =>
    intros E τ𝕖 HE
    apply Hctx; apply Hτ₀; apply Hτ₁
  case cons v γ τ𝕧 Γ Hvalue Hτv Hτγ IH =>
    have ⟨Hwbt, _⟩ := typing.wbt_pure_at_dyn _ _ _ _ Hτv
    have Hτ₀ : typing Γ 𝟚 (.app₁ (.lam {0 ↤ Γ.length}e₀) v) τ ∅ :=
      by
      rw [← union_pure_left ∅, ← union_pure_left ∅]
      apply typing.app₁
      apply typing.lam
      rw [identity.opening_closing _ _ _ (typing.regular _ _ _ _ _ Hτ₀)]
      . apply Hτ₀
      . apply Hwbt
      . rw [← closed.under_closing]
        apply typing.closed_at_env _ _ _ _ _ Hτ₀
      rw [← List.append_nil Γ]
      apply typing.weakening [] Γ _ _ _ _ Hτv
    have Hτ₁ : typing Γ 𝟚 (.app₁ (.lam {0 ↤ Γ.length}e₁) v) τ ∅ :=
      by
      rw [← union_pure_left ∅, ← union_pure_left ∅]
      apply typing.app₁
      apply typing.lam
      rw [identity.opening_closing _ _ _ (typing.regular _ _ _ _ _ Hτ₁)]
      . apply Hτ₁
      . apply Hwbt
      . rw [← closed.under_closing]
        apply typing.closed_at_env _ _ _ _ _ Hτ₁
      rw [← List.append_nil Γ]
      apply typing.weakening [] Γ _ _ _ _ Hτv
    admit
