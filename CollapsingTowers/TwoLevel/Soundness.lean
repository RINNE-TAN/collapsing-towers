
import CollapsingTowers.TwoLevel.Progresss
import CollapsingTowers.TwoLevel.Preservation
@[simp]
def stuck (st₀ : Store) (e₀ : Expr) : Prop :=
  ¬(∃ st₁ e₁, step (st₀, e₀) (st₁, e₁)) /\ ¬value e₀

theorem stepn_preservation : ∀ st₀ st₁ e₀ e₁ τ, stepn (st₀, e₀) (st₁, e₁) -> typing [] e₀ τ -> typing [] e₁ τ :=
  by
  intro st₀ st₁ e₀ e₁ τ Hstepn Hτ
  generalize HEq₀ : (st₀, e₀) = E₀
  generalize HEq₁ : (st₁, e₁) = E₁
  rw [HEq₀, HEq₁] at Hstepn
  induction Hstepn generalizing st₀ st₁ e₀ e₁ with
  | refl =>
    simp at HEq₁ HEq₀
    rw [HEq₁.right]
    rw [HEq₀.right] at Hτ
    apply Hτ
  | multi _ _ _ _ _ _ _ Hstep IHτ =>
    simp at HEq₁ HEq₀
    rw [HEq₁.right]
    rw [HEq₀.right] at Hτ
    apply preservation; apply Hstep
    apply IHτ; apply Hτ; repeat rfl

theorem soundness : ∀ st₀ st₁ e₀ e₁ τ, stepn (st₀, e₀) (st₁, e₁) -> typing [] e₀ τ -> ¬stuck st₁ e₁ :=
  by
  intros st₀ st₁ e₀ e₁ τ Hstepn Hτ
  simp; intro HNorm
  cases progress st₁ _ _ (stepn_preservation _ _ _ _ _ Hstepn Hτ) with
  | inl Hvalue => apply Hvalue
  | inr Hstep =>
    have ⟨_, _, Hstep⟩ := Hstep
    exfalso; apply HNorm; apply Hstep
