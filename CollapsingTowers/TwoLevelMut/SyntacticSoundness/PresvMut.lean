import CollapsingTowers.TwoLevelMut.SyntacticSoundness.PresvCtx

theorem preservation.mutable.head :
  ∀ σ₀ σ₁ Γ e₀ e₁ τ φ,
    head_mutable ⟨σ₀, e₀⟩ ⟨σ₁, e₁⟩ →
    ok σ₀ →
    typing σ₀ Γ 𝟙 e₀ τ φ →
    ok σ₁ ∧
    typing σ₁ Γ 𝟙 e₁ τ φ :=
  by
  intros σ₀ σ₁ Γ e₀ e₁ τ φ Hmut Hok₀ Hτ
  cases Hmut
  case alloc₁ v Hvalue =>
    cases Hτ
    case alloc₁ Hτe =>
    cases Hvalue <;> try contradiction
    case lit n =>
      constructor
      . apply ok.cons _ _ Hok₀
      . cases Hτe; apply typing.loc; simp
  case load₁ l Hbinds =>
    cases Hτ
    case load₁ Hτe =>
    constructor
    . apply Hok₀
    . have ⟨n, HEq⟩ := ok.binds _ _ _ Hok₀ Hbinds
      rw [← HEq]
      cases Hτe; apply typing.lit
  case store₁ l v Hvalue Hpatch =>
    cases Hτ
    case store₁ Hτl Hτr =>
    cases Hvalue <;> try contradiction
    case lit n =>
      constructor
      . apply ok.patch _ _ _ _ Hpatch Hok₀
      . cases Hτl; cases Hτr; apply typing.unit

theorem preservation.mutable :
  ∀ σ₀ σ₁ Γ M e₀ e₁ τ φ,
    ctx𝕄 Γ.length M →
    lc e₀ →
    head_mutable ⟨σ₀, e₀⟩ ⟨σ₁, e₁⟩ →
    ok σ₀ →
    typing σ₀ Γ 𝟙 M⟦e₀⟧ τ φ →
    ok σ₁ ∧
    typing σ₁ Γ 𝟙 M⟦e₁⟧ τ φ :=
  by
  intros σ₀ σ₁ Γ M e₀ e₁ τ φ HM Hlc Hmut Hok₀ Hτ
  generalize HEqlvl : Γ.length = lvl
  rw [HEqlvl] at HM
  have Hσ := head_mutable.store_grow _ _ _ _ Hmut
  induction HM generalizing Γ τ φ
  case hole => apply preservation.mutable.head _ _ _ _ _ _ _ Hmut Hok₀ Hτ
  case cons𝔹 B M HB HM IH =>
    have ⟨τ𝕖, φ₁, φ₂, HEqφ, Hτ, IHτB⟩ := preservation.under_ctx𝔹 _ _ _ _ _ _ HB Hτ
    rw [HEqφ]
    have ⟨Hok₁, Hτ⟩ := IH _ _ _ Hτ HEqlvl
    have Hτ := IHτB _ ⦰ _ _ Hσ Hτ
    constructor
    . apply Hok₁
    . apply Hτ
  case consℝ R M HR HM IH =>
    rw [← HEqlvl] at HR IH
    have Hlc : lc M⟦e₀⟧ := lc.under_ctx𝕄 _ _ _ _ HM Hlc
    have Hfv : fv M⟦e₁⟧ ⊆ fv M⟦e₀⟧ := fv.under_ctx𝕄 _ _ _ _ HM (head_mutable.fv_shrink _ _ _ _ Hok₀ Hmut)
    have ⟨Δ, τ𝕖, φ₁, HEqΓ, Hτ, IHτR⟩ := preservation.under_ctxℝ _ _ _ _ _ _ _ HR Hlc Hτ
    cases Hτ
    case pure Hτ =>
      have ⟨Hok₁, Hτ⟩ := IH _ _ _ Hτ HEqΓ
      have Hτ := IHτR σ₁ _ _ Hσ Hfv (typing_reification.pure _ _ _ _ Hτ)
      constructor
      . apply Hok₁
      . apply Hτ
    case reify Hτ =>
      have ⟨Hok₁, Hτ⟩ := IH _ _ _ Hτ HEqΓ
      have Hτ := IHτR σ₁ _ _ Hσ Hfv (typing_reification.reify _ _ _ _ _ Hτ)
      constructor
      . apply Hok₁
      . apply Hτ
