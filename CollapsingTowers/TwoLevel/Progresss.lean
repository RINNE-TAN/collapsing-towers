
import CollapsingTowers.TwoLevel.Typing
@[simp]
def closed_at_code (e : Expr) (x : ℕ) : Prop :=
  match e with
  | .bvar _ => true
  | .fvar _ => false
  | .lam₁ e => closed_at_code e x
  | .lam₂ e => closed_at_code e x
  | .app₁ e1 e2 => closed_at_code e1 x ∧ closed_at_code e2 x
  | .app₂ e1 e2 => closed_at_code e1 x ∧ closed_at_code e2 x
  | .lit₁ _ => true
  | .lit₂ n => closed_at_code n x
  | .plus₁ l r => closed_at_code l x ∧ closed_at_code r x
  | .plus₂ l r => closed_at_code l x ∧ closed_at_code r x
  | .code e => closed_at e x
  | .reflect e => closed_at e x
  | .lam𝕔 e => closed_at_code e x
  | .lets b e => closed_at_code b x ∧ closed_at_code e x
  | .let𝕔 b e => closed_at b x ∧ closed_at_code e x

theorem progress_strengthened : ∀ Γ e₀ τ, typing Γ e₀ τ -> closed_at_code e₀ Γ.length -> value e₀ \/ ∃ e₁, step e₀ e₁ :=
  by
  intros Γ e₀ τ Hτ Hclose
  induction Hτ with
  | fvar => nomatch Hclose
  | lam𝕔 Γ e _ _ Hτe Hclose IH =>
    right
    simp at Hclose
    admit
  | lam₂ _ _ _ _ Hτe Hclose IH =>
    right
    admit
  | _ => admit

theorem progress : ∀ e₀ τ, typing [] e₀ τ -> wfty τ -> value e₀ \/ ∃ e₁, step e₀ e₁ := by admit
