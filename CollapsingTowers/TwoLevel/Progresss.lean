
import CollapsingTowers.TwoLevel.Typing
theorem progress_strengthened : ∀ Γ e₀ τ, typing_strengthened Γ e₀ τ -> value e₀ \/ ∃ e₁, step_lvl Γ.length e₀ e₁ :=
  by
  intros Γ e₀ τ Hτ
  admit

theorem progress : ∀ e₀ τ, typing [] e₀ τ -> value e₀ \/ ∃ e₁, step e₀ e₁ :=
  by
  intros _ _ Hτ
  rw [step, ← List.length_nil]
  apply progress_strengthened
  apply typing_weakening_empty
  apply Hτ
