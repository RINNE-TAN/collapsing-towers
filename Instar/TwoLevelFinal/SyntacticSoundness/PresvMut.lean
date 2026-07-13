import Instar.TwoLevelFinal.SyntacticSoundness.PresvCtx

theorem preservation.mutable.head :
  ∀ σ₀ σ₁ Γ e₀ e₁ τ ε,
    head_mutable ⟨σ₀, e₀⟩ ⟨σ₁, e₁⟩ →
    ¬typing Γ 𝟙 e₀ τ ε :=
  by
  intros σ₀ σ₁ Γ e₀ e₁ τ ε Hmut Hτ
  cases Hmut <;> contradiction

theorem preservation.mutable :
  ∀ σ₀ σ₁ Γ M e₀ e₁ τ ε,
    ctx𝕄 Γ.length M →
    lc e₀ →
    head_mutable ⟨σ₀, e₀⟩ ⟨σ₁, e₁⟩ →
    ¬typing Γ 𝟙 M⟦e₀⟧ τ ε :=
  by
  intros σ₀ σ₁ Γ M e₀ e₁ τ ε HM Hlc Hmut Hτ
  generalize HEqlvl : Γ.length = lvl
  rw [HEqlvl] at HM
  induction HM generalizing Γ τ ε
  case hole => apply preservation.mutable.head _ _ _ _ _ _ _ Hmut Hτ
  case cons𝔹 B M HB HM IH =>
    have ⟨τ𝕖, ε₁, ε₂, HEqε, Hτ, IHτB⟩ := preservation.under_ctx𝔹 _ _ _ _ _ HB Hτ
    apply IH _ _ _ Hτ HEqlvl
  case consℝ R M HR HM IH =>
    rw [← HEqlvl] at HR IH
    have Hlc : lc M⟦e₀⟧ := lc.under_ctx𝕄 _ _ _ _ HM Hlc
    have Hfv : fv M⟦e₁⟧ ⊆ fv M⟦e₀⟧ := fv.under_ctx𝕄 _ _ _ _ HM (head_mutable.fv_shrink _ _ _ _ Hmut)
    have Hsf : store_free M⟦e₀⟧ → store_free M⟦e₁⟧ :=
      by
      intros HsfM; exfalso
      apply store_free.under_head_mutable _ _ _ _ Hmut
      apply store_free.decompose_ctx𝕄 _ _ _ HM HsfM
    have ⟨Δ, τ𝕖, ε₁, HEqΓ, Hτ, IHτR⟩ := preservation.under_ctxℝ _ _ _ _ _ _ HR Hlc Hτ
    cases Hτ
    all_goals
      next Hτ => apply IH _ _ _ Hτ HEqΓ
