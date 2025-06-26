
import CollapsingTowers.TwoLevelPCP.Typing
import CollapsingTowers.TwoLevelPCP.Preservation.Subst
theorem preservation_head𝕄 :
  ∀ Γ σ e₀ e₁ τ φ₀,
    head𝕄 e₀ e₁ →
    lc e₀ →
    typing Γ σ .stat e₀ τ φ₀ →
    ∃ φ₁,
      typing Γ σ .stat e₁ τ φ₁ ∧
      φ₁ ≤ φ₀ :=
  by
  intros Γ σ e₀ e₁ τ φ₀ Hhead Hlc Hτ
  cases Hhead
  case lets Hvalue =>
    exists φ₀; constructor
    cases Hτ
    case lets e v τ φ _ _ Hτv Hclose Hτe =>
      have Hpure : φ = ∅ := by
        apply typing_value_pure
        apply Hτv; apply Hvalue
      rw [Hpure] at Hτv; rw [Hpure, open_subst, union_pure_left]
      rw [← subst_intro]; apply preservation_subst
      apply Hτv; apply Hτe; apply Hclose
    rfl
  case app₁ Hvalue =>
    exists φ₀; constructor
    cases Hτ
    case app₁ φ Hτv Hτf =>
      cases Hτf
      case lam₁ Hclose _ Hτe =>
        have Hpure : φ = ∅ := by
          apply typing_value_pure
          apply Hτv; apply Hvalue
        rw [Hpure] at Hτv; rw [Hpure, open_subst, union_pure_right, union_pure_right]
        rw [← subst_intro]; apply preservation_subst
        apply Hτv; apply Hτe; apply Hclose
    rfl
  case app₂ =>
    exists φ₀; constructor
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
    rfl
  case binary₁ =>
    exists φ₀; constructor
    cases Hτ
    case binary₁ Hl Hr =>
      cases Hl; cases Hr; apply typing.lit₁
    rfl
  case binary₂ =>
    exists φ₀; constructor
    cases Hτ
    case binary₂ Hτ₀ Hτ₁ =>
      cases Hτ₀
      case code_fragment HwellBinds₀ Hbinds₀ =>
        cases Hτ₁
        case code_fragment HwellBinds₁ Hbinds₁ =>
          apply typing.reflect
          rw [← union_pure_right ∅, ← union_pure_right (∅ ∪ ∅)]
          apply typing.binary₁
          apply typing.fvar; apply Hbinds₀; apply HwellBinds₀
          apply typing.fvar; apply Hbinds₁; apply HwellBinds₁
    rfl
  case lift_lit =>
    exists φ₀; constructor
    cases Hτ
    case lift_lit Hτ =>
      apply typing.reflect
      apply typing.lit₁
    case lift_lam => contradiction
    rfl
  case lift_lam e =>
    exists φ₀; constructor
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
    rfl
  case lam𝕔 e =>
    exists φ₀; constructor
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
    rfl
  case let𝕔 e =>
    exists φ₀; constructor
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
    rfl
  case run =>
    exists φ₀; constructor
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
    rfl
  case load₂ =>
    exists φ₀; constructor
    cases Hτ
    case load₂ Hτ =>
      cases Hτ
      case code_fragment HwellBinds Hbinds =>
        apply typing.reflect
        apply typing.load₁
        apply typing.fvar; apply Hbinds; apply HwellBinds
    rfl
  case alloc₂ =>
    exists φ₀; constructor
    cases Hτ
    case alloc₂ Hτ =>
      cases Hτ
      case code_fragment HwellBinds Hbinds =>
        apply typing.reflect
        apply typing.alloc₁
        apply typing.fvar; apply Hbinds; apply HwellBinds
    rfl
  case store₂ =>
    exists φ₀; constructor
    cases Hτ
    case store₂ Hτ₀ Hτ₁ =>
      cases Hτ₀
      case code_fragment HwellBinds₀ Hbinds₀ =>
        cases Hτ₁
        case code_fragment HwellBinds₁ Hbinds₁ =>
          apply typing.reflect
          rw [← union_pure_right ∅, ← union_pure_right (∅ ∪ ∅)]
          apply typing.store₁
          apply typing.fvar; apply Hbinds₀; apply HwellBinds₀
          apply typing.fvar; apply Hbinds₁; apply HwellBinds₁
    rfl
  case ifz₁_left =>
    exists φ₀; constructor
    cases Hτ
    case ifz₁ φ _ Hτv Hτl Hτr =>
        have Hpure : φ = ∅ := by
          apply typing_value_pure
          apply Hτv; constructor
        rw [Hpure, union_pure_left]; apply Hτl
    rfl
  case ifz₁_right =>
    exists φ₀; constructor
    cases Hτ
    case ifz₁ φ _ Hτv Hτl Hτr =>
        have Hpure : φ = ∅ := by
          apply typing_value_pure
          apply Hτv; constructor
        rw [Hpure, union_pure_left]; apply Hτr
    rfl
  case ifz₂ =>
    exists φ₀; constructor
    cases Hτ
    case ifz₂ Hτc Hτl Hτr =>
      cases Hτc
      case code_fragment HwellBinds Hbinds =>
        apply typing.reflect; rw [← union_pure_right ∅]
        apply typing.ifz₁
        apply typing.fvar; apply Hbinds; apply HwellBinds
        cases Hτl with
        | pure _ _ _ _ Hτl =>
          cases Hτl; assumption
        | reify _ _ _ _ _ Hτl =>
          cases Hτl; apply typing.fvar
          assumption; assumption
        cases Hτr with
        | pure _ _ _ _ Hτr =>
          cases Hτr; assumption
        | reify _ _ _ _ _ Hτr =>
          cases Hτr; apply typing.fvar
          assumption; assumption
    rfl
  case fix₁ =>
    exists φ₀; constructor
    cases Hτ
    case fix₁ Hτ =>
      cases Hτ
      case lam₁ e Hclose HwellBinds Hτe =>
        rw [open_subst, ← subst_intro]; apply preservation_subst
        apply typing.fix₁; apply typing.lam₁
        apply Hτe; apply HwellBinds; apply Hclose
        apply Hτe; apply Hclose
    rfl
  case fix₂ =>
    exists φ₀; constructor
    cases Hτ
    case fix₂ Hτ =>
      cases Hτ
      case code_fragment HwellBinds Hbinds =>
        apply typing.reflect
        apply typing.fix₁
        apply typing.fvar; apply Hbinds; apply HwellBinds
    rfl
