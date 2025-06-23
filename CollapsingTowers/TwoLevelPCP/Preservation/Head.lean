
import CollapsingTowers.TwoLevelPCP.Typing
import CollapsingTowers.TwoLevelPCP.Preservation.Subst
theorem preservation_head𝕄 :
  ∀ Γ σ e₀ e₁ τ φ,
    head𝕄 e₀ e₁ →
    lc e₀ →
    typing Γ σ .stat e₀ τ φ →
    typing Γ σ .stat e₁ τ φ :=
  by
  intros Γ σ e₀ e₁ τ φ Hhead Hlc Hτ
  cases Hhead
  case lets Hvalue =>
    cases Hτ
    case lets e v τ φ _ _ Hτv Hclose
      Hτe =>
      have Hpure : φ = ∅ := by
        apply typing_value_pure
        apply Hτv; apply Hvalue
      rw [Hpure] at Hτv; rw [Hpure, open_subst, union_pure_left]
      rw [← subst_intro]; apply preservation_subst
      apply Hτv; apply Hτe; apply Hclose
  case app₁ Hvalue =>
    cases Hτ
    case app₁ φ Hτv Hτf =>
      cases Hτf
      case lam₁ Hclose _
        Hτe =>
        have Hpure : φ = ∅ := by
          apply typing_value_pure
          apply Hτv; apply Hvalue
        rw [Hpure] at Hτv; rw [Hpure, open_subst, union_pure_right, union_pure_right]
        rw [← subst_intro]; apply preservation_subst
        apply Hτv; apply Hτe; apply Hclose
  case app₂ =>
    cases Hτ
    case app₂ Hτ₀ Hτ₁ =>
      cases Hτ₀
      case code_fragment HwellBinds₀ Hbinds₀ =>
        cases Hτ₁
        case code_fragment HwellBinds₁ Hbinds₁ =>
          apply typing.reflect
          rw [← union_pure_right ∅, ← union_pure_right (∅ ∪ ∅)]
          apply typing.app₁
          apply typing.fvar; apply Hbinds₀; apply HwellBinds₀
          apply typing.fvar; apply Hbinds₁; apply HwellBinds₁
  case plus₁ =>
    cases Hτ
    case plus₁ Hl Hr =>
      cases Hl; cases Hr; apply typing.lit₁
  case plus₂ =>
    cases Hτ
    case plus₂ Hτ₀ Hτ₁ =>
      cases Hτ₀
      case code_fragment HwellBinds₀ Hbinds₀ =>
        cases Hτ₁
        case code_fragment HwellBinds₁ Hbinds₁ =>
          apply typing.reflect
          rw [← union_pure_right ∅, ← union_pure_right (∅ ∪ ∅)]
          apply typing.plus₁
          apply typing.fvar; apply Hbinds₀; apply HwellBinds₀
          apply typing.fvar; apply Hbinds₁; apply HwellBinds₁
  case lift_lit =>
    cases Hτ
    case lift_lit Hτ =>
      apply typing.reflect
      apply typing.lit₁
    case lift_lam => contradiction
  case lift_lam e =>
    cases Hτ
    case lift_lit => contradiction
    case lift_lam Hτ =>
      cases Hτ
      case lam₁ Hclose HwellBinds Hτe =>
        rw [← map𝕔₀_intro Γ.length]
        apply typing.lam𝕔
        simp; rw [open_close_id]
        apply typing_reification.reify
        apply preservation_maping
        apply Hτe
        apply typing.code_fragment; simp
        apply HwellBinds
        apply subst_closedb_at; simp; apply (open_closedb _ _ _).mpr; apply Hlc
        apply HwellBinds
        apply (close_closed _ _ _).mp; apply subst_closed_at; simp; apply open_closed; apply Hclose
        apply Hclose
  case lam𝕔 e =>
    cases Hτ
    case lam𝕔 HwellBinds Hclose Hτ =>
      apply typing.reflect
      apply typing.lam₁
      cases Hτ with
      | pure _ _ _ _ Hτ =>
        simp at *
        generalize Eqe : opening 0 (.fvar (List.length Γ)) e = E
        rw [Eqe] at Hτ
        cases Hτ with
        | code_rep _ _ _ _ Hτ => apply Hτ
      | reify _ _ _ _ _ Hτ =>
        simp at *
        generalize Eqe : opening 0 (.fvar (List.length Γ)) e = E
        rw [Eqe] at Hτ
        cases Hτ with
        | code_fragment _ _ _ _ Hbinds HwellBinds =>
          apply typing.fvar
          apply Hbinds; apply HwellBinds
      apply HwellBinds
      apply Hclose
  case let𝕔 e =>
    cases Hτ
    case let𝕔 HwellBinds Hτb Hclose Hτe =>
      apply typing.code_rep
      rw [← union_pure_right ∅]
      apply typing.lets
      apply Hτb
      cases Hτe with
      | pure _ _ _ _ Hτ =>
        simp at *
        generalize Eqe : opening 0 (.fvar (List.length Γ)) e = E
        rw [Eqe] at Hτ
        cases Hτ with
        | code_rep _ _ _ _ Hτ => apply Hτ
      | reify _ _ _ _ _ Hτ =>
        simp at *
        generalize Eqe : opening 0 (.fvar (List.length Γ)) e = E
        rw [Eqe] at Hτ
        cases Hτ with
        | code_fragment _ _ _ _ Hbinds HwellBinds =>
          apply typing.fvar
          apply Hbinds; apply HwellBinds
      apply HwellBinds
      apply Hclose
  case run =>
    cases Hτ
    case run Hclose Hτ =>
      cases Hτ with
      | pure _ _ _ _ Hτ =>
        cases Hτ
        case code_rep Hτ =>
          apply typing_escape
          apply Hclose; apply Hτ
      | reify _ _ _ _ _ Hτ =>
        cases Hτ; contradiction
  case load₂ =>
    cases Hτ
    case load₂ Hτ =>
      cases Hτ
      case code_fragment HwellBinds Hbinds =>
        apply typing.reflect
        apply typing.load₁
        apply typing.fvar; apply Hbinds; apply HwellBinds
  case alloc₂ =>
    cases Hτ
    case alloc₂ Hτ =>
      cases Hτ
      case code_fragment HwellBinds Hbinds =>
        apply typing.reflect
        apply typing.alloc₁
        apply typing.fvar; apply Hbinds; apply HwellBinds
