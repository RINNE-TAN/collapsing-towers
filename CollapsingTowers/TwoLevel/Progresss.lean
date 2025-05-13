
import CollapsingTowers.TwoLevel.Typing
@[simp]
def env_wfty₁ : TEnv -> Prop
  | [] => true
  | τ :: τs => wfty₁ τ /\ env_wfty₁ τs

theorem progress𝕔 : ∀ Γ e₀ τ, typing Γ e₀ (.rep τ) -> env_wfty₁ Γ -> wfty₁ τ -> value e₀ \/ ∃ e₁, step e₀ e₁ :=
  by
  intros Γ e₀ τ
  generalize Eqτ : τ.rep = τ𝕔
  intros Hτ HwftyΓ Hwfty
  induction Hτ generalizing τ with
  | fvar _ _ _ Hbinds => admit
  | lam𝕔 Γ e _ _ Hτe Hclose IH =>
    right
    rw [← close_open_id₀ e Γ.length]
    generalize HEqe : open₀ Γ.length e = e𝕠
    rw [HEqe] at IH Hτe
    simp at IH Eqτ; rw [Eqτ] at Hwfty
    cases IH Hwfty.left HwftyΓ Hwfty.right with
    | inl Hvalue => admit
    | inr Hstep => admit
    apply Hclose
  | _ => admit

theorem progress : ∀ e₀ τ, typing [] e₀ τ -> wfty τ -> value e₀ \/ ∃ e₁, step e₀ e₁ := by admit
