import CollapsingTowers.TwoLevelRec.SyntacticSoundness.PresvHead

theorem preservation.strengthened :
  ∀ Γ e₀ e₁ τ φ₀,
    step_lvl Γ.length e₀ e₁ →
    typing Γ 𝟚 e₀ τ φ₀ →
    ∃ φ₁,
      typing Γ 𝟚 e₁ τ φ₁ ∧
      φ₁ ≤ φ₀ :=
  by
  intro Γ e₀ e₁ τ φ₀
  generalize HEqlvl : Γ.length = lvl
  intro Hstep Hτ
  cases Hstep
  case pure HM Hlc Hhead =>
    induction HM generalizing Γ τ φ₀
    case hole => apply preservation.head _ _ _ _ _ Hhead Hτ
    case cons𝔹 => admit
    case consℝ => admit
  case reflect P E e HP HE Hlc =>
    admit
