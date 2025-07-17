
import CollapsingTowers.TwoLevelBasic.Preservation.Head
import CollapsingTowers.TwoLevelBasic.Preservation.Reflect
theorem preservation_strengthened :
  ∀ Γ e₀ e₁ τ φ₀,
    step_lvl Γ.length e₀ e₁ →
    typing_reification Γ e₀ τ φ₀ →
    ∃ φ₁,
      typing_reification Γ e₁ τ φ₁ ∧
      φ₁ ≤ φ₀ :=
  by
  intro Γ e₀ e₁ τ φ₀ Hstep Hτ
  cases Hstep
  case step𝕄 HM Hlc Hhead𝕄 =>
    exists φ₀
    cases Hτ
    all_goals
      next Hτ =>
      simp; constructor
      apply decompose𝕄
      apply HM; apply Hlc
      apply fv_head𝕄; apply Hhead𝕄; intros _ _ _
      apply preservation_head𝕄; apply Hhead𝕄; apply Hlc
      apply Hτ
  case reflect P E e HP HE Hlc =>
    cases HP
    case hole =>
      exists ∅; constructor
      simp; apply preservation_reflect
      apply HE; apply Hτ; simp
    case consℚ HQ =>
      exists φ₀
      cases Hτ
      all_goals
        next Hτ =>
        simp; constructor
        apply decomposeℚ_reflect
        apply HQ; apply HE; apply Hlc; apply Hτ

theorem preservation :
  ∀ e₀ e₁ τ φ₀,
    step e₀ e₁ →
    typing_reification [] e₀ τ φ₀ →
    ∃ φ₁,
      typing_reification [] e₁ τ φ₁ ∧
      φ₁ ≤ φ₀ :=
  by
  intros e₀ e₁ τ φ₀ Hstep
  apply preservation_strengthened
  apply Hstep

theorem preservation_stepn :
  ∀ e₀ e₁ τ φ₀,
    stepn e₀ e₁ →
    typing_reification [] e₀ τ φ₀ →
    ∃ φ₁,
      typing_reification [] e₁ τ φ₁ ∧
      φ₁ ≤ φ₀ :=
  by
  intro e₀ e₁ τ φ₀ Hstepn Hτ
  induction Hstepn with
  | refl => exists φ₀
  | multi _ _ _ Hstep IH =>
    have ⟨φ₁, IHτ₁, HφLe₁⟩ := IH
    have ⟨φ₂, IHτ₂, HφLe₂⟩ := preservation _ _ _ _ Hstep IHτ₁
    exists φ₂
    constructor
    . apply IHτ₂
    . apply le_trans; apply HφLe₂; apply HφLe₁
