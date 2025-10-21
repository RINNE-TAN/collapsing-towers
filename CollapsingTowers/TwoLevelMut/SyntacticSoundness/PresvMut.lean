import CollapsingTowers.TwoLevelMut.SyntacticSoundness.PresvCtx

theorem preservation.mutable.head :
  ∀ σ₀ σ₁ Γ e₀ e₁ τ φ ω,
    head_mutable ⟨σ₀, e₀⟩ ⟨σ₁, e₁⟩ →
    ok σ₀ →
    typing σ₀ Γ 𝟙 e₀ τ φ ω →
    ok σ₁ ∧
    typing σ₁ Γ 𝟙 e₁ τ φ ∅ :=
  by
  intros σ₀ σ₁ Γ e₀ e₁ τ φ ω Hmut Hok₀ Hτ
  cases Hmut
  case alloc₁ n =>
    cases Hτ
    case alloc₁ Hτe =>
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
  case store₁ l n Hpatch =>
    cases Hτ
    case store₁ Hτl Hτr =>
      constructor
      . apply ok.patch _ _ _ _ Hpatch Hok₀
      . cases Hτl; cases Hτr; apply typing.unit
