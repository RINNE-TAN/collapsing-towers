import CollapsingTowers.TwoLevelMut.SyntacticTyping.Defs

lemma preservation.under_ctx𝔹 :
  ∀ σ₀ Γ B e₀ τ φ,
    ctx𝔹 B →
    typing σ₀ Γ 𝟙 B⟦e₀⟧ τ φ →
    ∃ τ𝕖 φ₀ φ𝔹,
      φ = φ₀ ∪ φ𝔹 ∧
      typing σ₀ Γ 𝟙 e₀ τ𝕖 φ₀ ∧
      ∀ σ₁ Δ e₁ φ₁,
        σ₀.length ≤ σ₁.length →
        typing σ₁ (Δ ++ Γ) 𝟙 e₁ τ𝕖 φ₁ →
        typing σ₁ (Δ ++ Γ) 𝟙 B⟦e₁⟧ τ (φ₁ ∪ φ𝔹) :=
  by
  intros σ₀ Γ B e₀ τ φ HB Hτ
  cases HB
  case appl₁ =>
    cases Hτ
    case app₁ τ𝕒 φ₀ φ₁ φ₂ Harg HX =>
      exists τ𝕒.arrow τ φ₀, φ₁, (φ₀ ∪ φ₂)
      constructor; cases φ₀ <;> cases φ₁ <;> cases φ₂ <;> simp
      constructor; apply HX
      intros σ₁ Δ e₁ φ₁ Hσ HX
      have HEqφ : φ₁ ∪ (φ₀ ∪ φ₂) = φ₀ ∪ φ₁ ∪ φ₂ := by cases φ₀ <;> cases φ₂ <;> simp
      rw [HEqφ]
      apply typing.app₁
      . apply HX
      . apply typing.weakening
        apply typing.weakening.store
        apply Hσ; apply Harg
  all_goals admit

lemma preservation.under_ctxℝ :
  ∀ σ₀ intro Γ R e₀ τ φ,
    ctxℝ intro Γ.length R →
    lc e₀ →
    typing σ₀ Γ 𝟙 R⟦e₀⟧ τ φ →
    ∃ Δ τ𝕖 φ₀,
      Δ.length = Γ.length + intro ∧
      typing_reification σ₀ Δ e₀ τ𝕖 φ₀ ∧
      ∀ σ₁ e₁ φ₁,
        σ₀.length ≤ σ₁.length →
        fv e₁ ⊆ fv e₀ →
        typing_reification σ₁ Δ e₁ τ𝕖 φ₁ →
        typing σ₁ Γ 𝟙 R⟦e₁⟧ τ φ :=
  by
  intros σ₀ intro Γ R e₀ τ φ HR Hlc Hτ
  cases HR
  case lam𝕔 =>
    cases Hτ
    case lam𝕔 τ𝕒 τ𝕓 φ₀ Hwbt HX Hclosed =>
      rw [identity.opening_closing _ _ _ Hlc] at HX
      exists (τ𝕒, 𝟚) :: Γ, .rep τ𝕓, φ₀
      constructor; simp
      constructor; apply HX
      intros σ₁ e₁ φ₁ Hσ Hfv HX
      apply typing.lam𝕔
      . rw [identity.opening_closing _ _ _ (typing_reification.regular _ _ _ _ _ HX)]
        apply HX
      . apply Hwbt
      . rw [← closed.under_closing]
        apply typing_reification.closed_at_env _ _ _ _ _ HX
  case lets𝕔 =>
    cases Hτ
    case lets𝕔 τ𝕒 τ𝕓 φ₀ Hwbt Hb HX Hclosed =>
      rw [identity.opening_closing _ _ _ Hlc] at HX
      exists (τ𝕒, 𝟚) :: Γ, .rep τ𝕓, φ₀
      constructor; simp
      constructor; apply HX
      intros σ₁ e₁ φ₁ Hσ Hfv HX
      apply typing.lets𝕔
      . apply typing.weakening.store _ _ _ _ _ _ _ Hσ Hb
      . rw [identity.opening_closing _ _ _ (typing_reification.regular _ _ _ _ _ HX)]
        apply HX
      . apply Hwbt
      . rw [← closed.under_closing]
        apply typing_reification.closed_at_env _ _ _ _ _ HX
  case run =>
    cases Hτ
    case run φ₀ Hclosed HX =>
      exists Γ, .rep τ, φ₀
      constructor; simp
      constructor; apply HX
      intros σ₁ e₁ φ₁ Hσ Hfv HX
      apply typing.run
      . apply HX
      . rw [closed_iff_fv_empty] at Hclosed
        simp [Hclosed] at Hfv
        rw [closed_iff_fv_empty, Hfv]

lemma preservation.under_ctx𝔼 :
  ∀ σ₀ Γ E e₀ τ φ₀,
    ctx𝔼 E →
    typing σ₀ Γ 𝟙 E⟦e₀⟧ τ φ₀ →
    ∃ τ𝕖 φ𝕖 φ𝔼,
      φ₀ = φ𝕖 ∪ φ𝔼 ∧
      typing σ₀ Γ 𝟙 e₀ τ𝕖 φ𝕖 ∧
      ∀ σ₁ Δ e₁ φ₁,
        σ₀.length ≤ σ₁.length →
        typing σ₁ (Δ ++ Γ) 𝟙 e₁ τ𝕖 φ₁ →
        typing σ₁ (Δ ++ Γ) 𝟙 E⟦e₁⟧ τ (φ₁ ∪ φ𝔼) :=
  by
  intros σ₀ Γ E e₀ τ φ₀ HE Hτ
  induction HE generalizing τ φ₀
  case hole =>
    exists τ, φ₀, ⊥
    constructor; cases φ₀ <;> rfl
    constructor; apply Hτ
    intros σ₁ Δ e φ Hσ; simp
  case cons𝔹 B E HB HE IH =>
    have ⟨τ𝕖, φ₀, φ₁, HEqφ₀, Hτ, IHτB⟩ := preservation.under_ctx𝔹 _ _ _ _ _ _ HB Hτ
    have ⟨τ𝕖, φ₂, φ₃, HEqφ₁, Hτ, IHτE⟩ := IH _ _ Hτ
    rw [HEqφ₀, HEqφ₁]
    exists τ𝕖, φ₂, φ₁ ∪ φ₃
    constructor; cases φ₀ <;> cases φ₁ <;> cases φ₂ <;> cases φ₃ <;> simp
    constructor; apply Hτ
    intros σ₁ Δ e φ Hσ Hτ
    have Hτ := IHτE _ _ _ _ Hσ Hτ
    have Hτ := IHτB _ _ _ _ Hσ Hτ
    have HEqφ : φ ∪ (φ₁ ∪ φ₃) = φ ∪ φ₃ ∪ φ₁ := by cases φ₁ <;> cases φ₃ <;> simp
    rw [HEqφ]; apply Hτ
