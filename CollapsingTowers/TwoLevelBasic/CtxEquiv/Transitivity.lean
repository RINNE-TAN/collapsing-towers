import CollapsingTowers.TwoLevelBasic.CtxEquiv.ObsCtx

-- Γ ⊧ e₀ ≈𝑐𝑡𝑥 e₁ : τ
-- Γ ⊧ e₁ ≈𝑐𝑡𝑥 e₂ : τ
-- ——————————————————
-- Γ ⊧ e₀ ≈𝑐𝑡𝑥 e₂ : τ
theorem ctx_equiv.trans :
  ∀ Γ e₀ e₁ e₂ τ,
    ctx_equiv Γ e₀ e₁ τ →
    ctx_equiv Γ e₁ e₂ τ →
    ctx_equiv Γ e₀ e₂ τ :=
  by
  intros Γ e₀ e₁ e₂ τ Hctx₀ Hctx₁
  have ⟨Hτ₀, Hτ₁, Hctx₀⟩ := Hctx₀
  have ⟨Hτ₁, Hτ₂, Hctx₁⟩ := Hctx₁
  constructor; apply Hτ₀
  constructor; apply Hτ₂
  intros C HC v Hvalue
  rw [Hctx₀ C HC v Hvalue]
  rw [Hctx₁ C HC v Hvalue]
