import CollapsingTowers.TwoLvLBasic.SyntacticTyping.PresvHead
import CollapsingTowers.TwoLvLBasic.SyntacticTyping.PresvReflect

theorem preservation :
  ∀ Γ e₀ e₁ τ φ₀,
    step_lvl Γ.length e₀ e₁ →
    typing_reification Γ e₀ τ φ₀ →
    ∃ φ₁,
      typing_reification Γ e₁ τ φ₁ ∧
      φ₁ ≤ φ₀ :=
  by
  intro Γ e₀ e₁ τ φ₀ Hstep Hτ
  cases Hstep
  case pure HM Hlc Hhead =>
    exists φ₀
    cases Hτ
    all_goals
      next Hτ =>
      simp; constructor
      apply preservation.under_ctx𝕄
      apply HM; apply Hlc
      apply head.fv_shrink; apply Hhead; intros _ _ _
      apply preservation.head; apply Hhead; apply Hlc
      apply Hτ
  case reflect P E e HP HE Hlc =>
    cases HP
    case hole =>
      exists ∅; constructor
      simp; apply preservation.reflect
      apply HE; apply Hτ; simp
    case consℚ HQ =>
      exists φ₀
      cases Hτ
      all_goals
        next Hτ =>
        simp; constructor
        apply preservation.under_ctxℚ
        apply HQ; apply HE; apply Hlc; apply Hτ

theorem preservation.step :
  ∀ e₀ e₁ τ φ₀,
    (e₀ ⇝ e₁) →
    typing_reification [] e₀ τ φ₀ →
    ∃ φ₁,
      typing_reification [] e₁ τ φ₁ ∧
      φ₁ ≤ φ₀ :=
  by
  intros e₀ e₁ τ φ₀ Hstep
  apply preservation
  apply Hstep

theorem preservation.stepn :
  ∀ e₀ e₁ τ φ₀,
    (e₀ ⇝* e₁) →
    typing_reification [] e₀ τ φ₀ →
    ∃ φ₁,
      typing_reification [] e₁ τ φ₁ ∧
      φ₁ ≤ φ₀ :=
  by
  intro e₀ e₁ τ φ₀ Hstepn Hτ
  induction Hstepn generalizing φ₀ with
  | refl => exists φ₀
  | multi _ _ _ Hstep _ IH =>
    have ⟨φ₁, IHτ₁, HφLe₁⟩ := preservation.step _ _ _ _ Hstep Hτ
    have ⟨φ₂, IHτ₂, HφLe₂⟩ := IH _ IHτ₁
    exists φ₂
    constructor
    . apply IHτ₂
    . apply le_trans; apply HφLe₂; apply HφLe₁
