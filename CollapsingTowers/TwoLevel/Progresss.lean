
import CollapsingTowers.TwoLevel.Typing
theorem progress_strengthened : ∀ Γ e₀ τ, typing Γ e₀ τ -> value e₀ \/ ∃ e₁, step e₀ e₁ :=
  by
  intros Γ e₀ τ Hτ
  induction Hτ with
  | _ => admit

theorem progress : ∀ e₀ τ, typing [] e₀ τ -> value e₀ \/ ∃ e₁, step e₀ e₁ := by admit
