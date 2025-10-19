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

theorem preservation.mutable :
  ∀ σ₀ σ₁ Γ M e₀ e₁ τ φ ω₀,
    ctx𝕄 Γ.length M →
    lc e₀ →
    head_mutable ⟨σ₀, e₀⟩ ⟨σ₁, e₁⟩ →
    ok σ₀ →
    typing σ₀ Γ 𝟙 M⟦e₀⟧ τ φ ω₀ →
    ok σ₁ ∧
    ∃ ω₁,
      typing σ₁ Γ 𝟙 M⟦e₁⟧ τ φ ω₁ ∧
      ω₁ ≤ ω₀ :=
  by
  intros σ₀ σ₁ Γ M e₀ e₁ τ φ ω₀ HM Hlc Hmut Hok₀ Hτ
  generalize HEqlvl : Γ.length = lvl
  rw [HEqlvl] at HM
  have Hσ := head_mutable.store_grow _ _ _ _ Hmut
  induction HM generalizing Γ τ φ ω₀
  case hole =>
    have ⟨Hok₁, Hτ⟩ := preservation.mutable.head _ _ _ _ _ _ _ _ Hmut Hok₀ Hτ
    constructor
    . apply Hok₁
    . exists ∅; simp
      apply Hτ
  case cons𝔹 B M HB HM IH =>
    have ⟨τ𝕖, φ₁, φ₂, ω₁, ω₂, HEqφ, HEqω, Hτ, IHτB⟩ := preservation.under_ctx𝔹 _ _ _ _ _ _ _ HB Hτ
    rw [HEqφ, HEqω]
    have ⟨Hok₁, ω₃, Hτ, HLeω⟩ := IH _ _ _ _ Hτ HEqlvl
    have Hτ := IHτB _ ⦰ _ _ _ Hσ Hτ
    constructor
    . apply Hok₁
    . exists ω₃ ∪ ω₂
      constructor
      . apply Hτ
      . apply Set.union_subset_union_left _ HLeω
  case consℝ R M HR HM IH =>
    admit
