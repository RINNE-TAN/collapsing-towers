import CollapsingTowers.TwoLevelMut.SyntacticTyping.Defs

lemma preservation.under_ctx𝔹 :
  ∀ σ₀ Γ B e τ φ,
    ctx𝔹 B →
    typing σ₀ Γ 𝟙 B⟦e⟧ τ φ →
    ∃ τ𝕖 φ𝕖 φ𝔹,
      φ = φ𝕖 ∪ φ𝔹 ∧
      typing σ₀ Γ 𝟙 e τ𝕖 φ𝕖 ∧
      ∀ σ₁ Δ e φ,
        σ₀.length ≤ σ₁.length →
        typing σ₁ (Δ ++ Γ) 𝟙 e τ𝕖 φ →
        typing σ₁ (Δ ++ Γ) 𝟙 B⟦e⟧ τ (φ ∪ φ𝔹) :=
  by
  intros σ₀ Γ B e τ φ HB Hτ
  cases HB
  case appl₁ =>
    cases Hτ
    case app₁ τ𝕒 φ₀ φ₁ φ₂ Harg HX =>
      exists τ𝕒.arrow τ φ₀, φ₁, (φ₀ ∪ φ₂)
      constructor; cases φ₀ <;> cases φ₁ <;> cases φ₂ <;> simp
      constructor; apply HX
      intros σ₁ Δ eₓ φ Hσ HX
      have HEqφ : φ ∪ (φ₀ ∪ φ₂) = φ₀ ∪ φ ∪ φ₂ := by cases φ₀ <;> cases φ₂ <;> simp
      rw [HEqφ]
      apply typing.app₁
      . apply HX
      . apply typing.weakening
        apply typing.weakening.store
        apply Hσ; apply Harg
  all_goals admit
