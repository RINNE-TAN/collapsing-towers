import CollapsingTowers.TwoLevelRec.SyntacticSoundness.PresvCtx
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
    case cons𝔹 B M HB HM IHM =>
      rw [← ctx_comp B M]
      apply preservation.under_ctx𝔹
      . apply HB
      . intros _ _; apply IHM; simp [HEqlvl]
      . apply Hτ
    case consℝ R M HR HM IHM =>
      rw [← ctx_comp R M]
      apply preservation.under_ctxℝ
      . rw [HEqlvl]; apply HR
      . apply lc.under_ctx𝕄; apply HM; apply Hlc
      . intros _ _ _ _; apply IHM
        simp; omega
      . apply fv.under_ctx𝕄; apply HM
        apply head.fv_shrink; apply Hhead
      . apply Hτ
  case reflect P E e HP HE Hlc =>
    cases HP
    case hole =>
      admit
    case consℚ HQ =>
      induction HQ generalizing Γ τ φ₀
      case holeℝ R HR =>
        apply preservation.under_ctxℝ _ _ _ (E (.reflect e))
        . rw [HEqlvl]; apply HR
        . apply lc.under_ctx𝔼; apply HE; apply Hlc
        . intros _ _ _ _ Hτ
          admit
        . simp; constructor
          . apply fv.decompose_ctx𝔼 _ (.reflect e); apply HE
          . apply fv.under_ctx𝔼; apply HE; simp
        . apply Hτ
      case cons𝔹 B Q HB HQ IHQ =>
        rw [← ctx_comp B Q]
        apply preservation.under_ctx𝔹 _ _ (Q (E (.reflect e)))
        . apply HB
        . intros _ _; apply IHQ; simp [HEqlvl]
        . apply Hτ
      case consℝ R Q HR HQ IHQ =>
        rw [← ctx_comp R Q]
        apply preservation.under_ctxℝ _ _ _ (Q (E (.reflect e)))
        . rw [HEqlvl]; apply HR
        . apply lc.under_ctxℚ; apply HQ
          apply lc.under_ctx𝔼; apply HE
          apply Hlc
        . intros _ _ _ _; apply IHQ
          simp; omega
        . apply fv.under_ctxℚ; apply HQ
          simp; constructor
          . apply fv.decompose_ctx𝔼 _ (.reflect e); apply HE
          . apply fv.under_ctx𝔼; apply HE; simp
        . apply Hτ
