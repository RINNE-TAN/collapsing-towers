import CollapsingTowers.TwoLevelRec.CtxEquiv.ObsCtx

-- Γ ⊧ e₀ ≤𝑐𝑡𝑥 e₁ : τ
-- Γ ⊧ e₁ ≤𝑐𝑡𝑥 e₂ : τ
-- ——————————————————
-- Γ ⊧ e₀ ≤𝑐𝑡𝑥 e₂ : τ
theorem ctx_approx.trans :
  ∀ Γ e₀ e₁ e₂ τ,
    ctx_approx Γ e₀ e₁ τ →
    ctx_approx Γ e₁ e₂ τ →
    ctx_approx Γ e₀ e₂ τ :=
  by
  intros Γ e₀ e₁ e₂ τ Hctx₀ Hctx₁
  have ⟨Hτ₀, Hτ₁, Hctx₀⟩ := Hctx₀
  have ⟨Hτ₁, Hτ₂, Hctx₁⟩ := Hctx₁
  constructor; apply Hτ₀
  constructor; apply Hτ₂
  intros C τ HC Htermination₀
  apply Hctx₁ _ _ HC
  apply Hctx₀ _ _ HC
  apply Htermination₀

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
  constructor
  . apply ctx_approx.trans _ _ _ _ _ Hctx₀.left Hctx₁.left
  . apply ctx_approx.trans _ _ _ _ _ Hctx₁.right Hctx₀.right
