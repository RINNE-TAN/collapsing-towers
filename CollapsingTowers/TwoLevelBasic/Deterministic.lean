
import CollapsingTowers.TwoLevelBasic.SmallStep
theorem deterministic :
  ∀ e₀ e₁ e₂,
    step e₀ e₁ →
    step e₀ e₂ →
    e₁ = e₂ :=
  by admit

theorem church_rosser_strengthened :
  ∀ e₀ l r,
    stepn e₀ l →
    stepn e₀ r →
    ∃ v,
      stepn l v ∧
      stepn r v :=
  by
  intros e₀ l r Hstepl Hstepr
  induction Hstepl generalizing r
  case refl =>
    exists r; constructor
    . apply Hstepr
    . apply stepn.refl
  case multi le₀ le₁ le₂ IHstepl IHstepln IH =>
    cases Hstepr
    case refl =>
      exists le₂; constructor
      . apply stepn.refl
      . apply stepn.multi; apply IHstepl; apply IHstepln
    case multi re₀ IHstepr IHsteprn =>
      apply IH
      rw [deterministic _ _ _ IHstepl IHstepr]
      apply IHsteprn

theorem value_termination : ∀ v e, value v → ¬step v e := by admit

theorem church_rosser :
  ∀ e v₀ v₁,
    stepn e v₀ →
    stepn e v₁ →
    value v₀ →
    value v₁ →
    v₀ = v₁ :=
  by
  intros e v₀ v₁ Hstep₀ Hstep₁ Hvalue₀ Hvalue₁
  have ⟨v, Hstep₀, Hstep₁⟩ := church_rosser_strengthened _ _ _ Hstep₀ Hstep₁
  cases Hstep₀
  case refl =>
    cases Hstep₁
    case refl => rfl
    case multi Hstep _ =>
      exfalso; apply value_termination
      apply Hvalue₁; apply Hstep
  case multi Hstep _ =>
    exfalso; apply value_termination
    apply Hvalue₀; apply Hstep
