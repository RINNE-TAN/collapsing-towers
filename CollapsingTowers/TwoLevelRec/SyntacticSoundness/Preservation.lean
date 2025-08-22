import CollapsingTowers.TwoLevelRec.SyntacticSoundness.PresvPure

theorem preservation.strengthened :
  ∀ Γ e₀ e₁ τ φ₀,
    step_lvl Γ.length e₀ e₁ →
    typing_reification Γ e₀ τ φ₀ →
    ∃ φ₁,
      typing_reification Γ e₁ τ φ₁ ∧
      φ₁ ≤ φ₀ :=
  by
  intro Γ e₀ e₁ τ φ₀
  intro Hstep Hτ
  cases Hstep
  case pure HM Hlc Hhead =>
    cases Hτ
    case pure Hτ =>
      have ⟨φ, Hτ, Hφ⟩ := preservation.pure _ _ _ _ _ _ HM Hlc Hhead Hτ
      cases φ <;> simp at Hφ
      exists ⊥; constructor
      . apply typing_reification.pure _ _ _ Hτ
      . simp
    case reify Hτ =>
      have ⟨φ, Hτ, Hφ⟩ := preservation.pure _ _ _ _ _ _ HM Hlc Hhead Hτ
      exists φ; constructor
      . apply typing_reification.reify _ _ _ _ Hτ
      . apply Hφ
  case reflect P E e HP HE Hlc =>
    admit

theorem preservation :
  ∀ e₀ e₁ τ φ₀,
    (e₀ ⇝ e₁) →
    typing_reification ⦰ e₀ τ φ₀ →
    ∃ φ₁,
      typing_reification ⦰ e₁ τ φ₁ ∧
      φ₁ ≤ φ₀ :=
  by
  intros e₀ e₁ τ φ₀ Hstep
  apply preservation.strengthened
  apply Hstep

theorem preservation.stepn :
  ∀ e₀ e₁ τ φ₀,
    (e₀ ⇝* e₁) →
    typing_reification ⦰ e₀ τ φ₀ →
    ∃ φ₁,
      typing_reification ⦰ e₁ τ φ₁ ∧
      φ₁ ≤ φ₀ :=
  by
  intro e₀ e₁ τ φ₀ Hstepn Hτ
  induction Hstepn generalizing φ₀ with
  | refl => exists φ₀
  | multi _ _ _ Hstep _ IH =>
    have ⟨φ₁, IHτ₁, Hφ₁⟩ := preservation _ _ _ _ Hstep Hτ
    have ⟨φ₂, IHτ₂, Hφ₂⟩ := IH _ IHτ₁
    exists φ₂
    constructor
    . apply IHτ₂
    . apply le_trans; apply Hφ₂; apply Hφ₁
