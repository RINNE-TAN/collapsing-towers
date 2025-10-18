import CollapsingTowers.TwoLevelMut.SyntacticTyping.Defs
import Mathlib.Tactic.CC

lemma preservation.under_ctx𝔹 :
  ∀ σ₀ Γ B e₀ τ φ ω,
    ctx𝔹 B →
    typing σ₀ Γ 𝟙 B⟦e₀⟧ τ φ ω →
    ∃ τ𝕖 φ₀ φ𝔹 ω₀ ω𝔹,
      φ = φ₀ ∪ φ𝔹 ∧
      ω = ω₀ ∪ ω𝔹 ∧
      typing σ₀ Γ 𝟙 e₀ τ𝕖 φ₀ ω₀ ∧
      ∀ σ₁ Δ e₁ φ₁ ω₁,
        σ₀.length ≤ σ₁.length →
        typing σ₁ (Δ ++ Γ) 𝟙 e₁ τ𝕖 φ₁ ω₁ →
        typing σ₁ (Δ ++ Γ) 𝟙 B⟦e₁⟧ τ (φ₁ ∪ φ𝔹) (ω₁ ∪ ω𝔹) :=
  by
  intros σ₀ Γ B e₀ τ φ ω HB Hτ
  cases HB
  case appl₁ =>
    cases Hτ
    case app₁ τ𝕒 φ₀ φ₁ φ₂ ω₀ ω₁ ω₂ Harg HX =>
      exists (.arrow τ𝕒 τ φ₀ ω₀), φ₁, (φ₀ ∪ φ₂), ω₁, (ω₀ ∪ ω₂)
      constructor; cases φ₀ <;> cases φ₁ <;> cases φ₂ <;> simp
      constructor; cc
      constructor; apply HX
      intros σ₁ Δ e₁ φ ω Hσ HX
      have HEqφ : φ ∪ (φ₀ ∪ φ₂) = φ₀ ∪ φ ∪ φ₂ := by cases φ₀ <;> cases φ₂ <;> simp
      have HEqω : ω ∪ (ω₀ ∪ ω₂) = ω₀ ∪ ω ∪ ω₂ := by cc
      rw [HEqφ, HEqω]
      apply typing.app₁
      . apply HX
      . apply typing.weakening.store _ _ _ _ _ _ _ _ Hσ
        apply typing.weakening _ _ _ _ _ _ _ _ Harg
  case appr₁ =>
    cases Hτ
    case app₁ τ𝕒 φ₀ φ₁ φ₂ ω₀ ω₁ ω₂ HX Hf =>
      exists τ𝕒, φ₂, (φ₀ ∪ φ₁), ω₂, (ω₀ ∪ ω₁)
      constructor; cases φ₀ <;> cases φ₁ <;> cases φ₂ <;> simp
      constructor; cc
      constructor; apply HX
      intros σ₁ Δ e₁ φ ω Hσ HX
      have HEqφ : φ ∪ (φ₀ ∪ φ₁) = φ₀ ∪ φ₁ ∪ φ := by cases φ₀ <;> cases φ₁ <;> simp
      have HEqω : ω ∪ (ω₀ ∪ ω₁) = ω₀ ∪ ω₁ ∪ ω := by cc
      rw [HEqφ, HEqω]
      apply typing.app₁
      . apply typing.weakening.store _ _ _ _ _ _ _ _ Hσ
        apply typing.weakening _ _ _ _ _ _ _ _ Hf
      . apply HX
  case appl₂ =>
    cases Hτ
    case app₂ τ𝕒 τ𝕓 φ₁ φ₂ ω₀ ω₁ ω₂ HX Harg =>
      exists .fragment (.arrow τ𝕒 τ𝕓 ⊥ ω₀), φ₁, ⊤, ω₁, (ω₀ ∪ ω₂)
      constructor; simp
      constructor; cc
      constructor; apply HX
      intros σ₁ Δ e₁ φ ω Hσ HX; simp
      have HEqω : ω ∪ (ω₀ ∪ ω₂) = ω₀ ∪ ω ∪ ω₂ := by cc
      rw [HEqω]
      apply typing.app₂
      . apply HX
      . apply typing.weakening.store _ _ _ _ _ _ _ _ Hσ
        apply typing.weakening _ _ _ _ _ _ _ _ Harg
  case appr₂ =>
    cases Hτ
    case app₂ τ𝕒 τ𝕓 φ₁ φ₂ ω₀ ω₁ ω₂ Hf HX =>
      exists .fragment τ𝕒, φ₂, ⊤, ω₂, (ω₀ ∪ ω₁)
      constructor; simp
      constructor; cc
      constructor; apply HX
      intros σ₁ Δ e₁ φ ω Hσ HX; simp
      have HEqω : ω ∪ (ω₀ ∪ ω₁) = ω₀ ∪ ω₁ ∪ ω := by cc
      rw [HEqω]
      apply typing.app₂
      . apply typing.weakening.store _ _ _ _ _ _ _ _ Hσ
        apply typing.weakening _ _ _ _ _ _ _ _ Hf
      . apply HX
  all_goals admit
