import CollapsingTowers.TwoLevelRec.SyntacticSoundness.PresvHead

theorem preservation.strengthened :
  ∀ Γ e₀ e₁ τ φ₀,
    step_lvl Γ.length e₀ e₁ →
    typing_reification Γ e₀ τ φ₀ →
    ∃ φ₁,
      typing_reification Γ e₁ τ φ₁ ∧
      φ₁ ≤ φ₀ :=
  by
  intro Γ e₀ e₁ τ φ₀
  generalize HEqlvl : Γ.length = lvl
  intro Hstep Hτ
  cases Hstep
  case pure HM Hlc Hhead =>
    admit
  case reflect P E e HP HE Hlc =>
    admit
