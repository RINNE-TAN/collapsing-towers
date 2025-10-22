import CollapsingTowers.TwoLevelMut.CtxEquiv.ObsCtx

-- Γ ⊧ e₀ ≈𝑐𝑡𝑥 e₁ : τ ! ω
-- Γ ⊧ e₁ ≈𝑐𝑡𝑥 e₂ : τ ! ω
-- ——————————————————————
-- Γ ⊧ e₀ ≈𝑐𝑡𝑥 e₂ : τ ! ω
theorem ctx_equiv.trans :
  ∀ Γ e₀ e₁ e₂ τ ω,
    ctx_equiv Γ e₀ e₁ τ ω →
    ctx_equiv Γ e₁ e₂ τ ω →
    ctx_equiv Γ e₀ e₂ τ ω :=
  by
  intros Γ e₀ e₁ e₂ τ ω Hctx₀ Hctx₁
  have ⟨Hτ₀, Hτ₁, Hctx₀⟩ := Hctx₀
  have ⟨Hτ₁, Hτ₂, Hctx₁⟩ := Hctx₁
  constructor; apply Hτ₀
  constructor; apply Hτ₂
  intros C ω𝕔 HC
  have ⟨σ₀, σl₁, v₀, Hvalue₀, Hstep₀, Hstepl₁⟩ := Hctx₀ _ _ HC
  have ⟨σr₁, σ₂, v₁, Hvalue₁, Hstepr₁, Hstep₂⟩ := Hctx₁ _ _ HC
  have HEq := stepn.unique_normal_forms _ _ _ _ _ _ Hstepl₁ Hstepr₁ Hvalue₀ Hvalue₁
  exists σ₀, σ₂, v₀
  simp [← HEq] at Hstep₂
  constructor; apply Hvalue₀
  constructor; apply Hstep₀; apply Hstep₂
