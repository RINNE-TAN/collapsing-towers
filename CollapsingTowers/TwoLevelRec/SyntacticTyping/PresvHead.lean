import CollapsingTowers.TwoLevelRec.Semantic.Defs
import CollapsingTowers.TwoLevelRec.SyntacticTyping.PresvSubst
import CollapsingTowers.TwoLevelRec.SyntacticTyping.PresvMaping
import CollapsingTowers.TwoLevelRec.SyntacticTyping.Shrinking

lemma typing.escape_strengthened :
  ∀ Γ e τ,
    typing Γ 𝟚 e τ ∅ →
    typing (escape Γ) 𝟙 e τ ∅ :=
  by
  generalize HEq𝕊 : 𝟚 = 𝕊
  intros Γ e τ Hτ
  apply
    @typing.rec
      (fun Γ 𝕊 e τ φ (H : typing Γ 𝕊 e τ φ) =>
          𝟚 = 𝕊 →
          typing (escape Γ) 𝟙 e τ φ)
      (fun Γ e τ φ (H : typing_reification Γ e τ φ) => true)
  <;> (intros; try contradiction)
  case fvar x _ Hbinds Hwbt HEq𝕊 =>
    apply typing.fvar
    apply binds.escape; apply Hbinds
    apply wbt.escape; apply Hwbt
  case fix Hwbt Hclose IH HEq𝕊 =>
    rw [← HEq𝕊, escape] at IH
    apply typing.fix; rw [← escape.length]
    apply IH; rfl
    apply wbt.escape; apply Hwbt
    rw [← escape.length]; apply Hclose
  case app₁ IHf IHarg HEq𝕊 =>
    apply typing.app₁
    apply IHf; apply HEq𝕊
    apply IHarg; apply HEq𝕊
  case lit => apply typing.lit
  case lets Hwbt Hclose IHb IHe HEq𝕊 =>
    rw [← HEq𝕊, escape] at IHe
    apply typing.lets
    apply IHb; apply HEq𝕊
    rw [← escape.length]; apply IHe; rfl
    apply wbt.escape; apply Hwbt
    rw [← escape.length]; apply Hclose
  case pure => simp
  case reify => simp
  apply Hτ; apply HEq𝕊

lemma typing.escape :
  ∀ Γ e τ,
    closed e →
    typing Γ 𝟚 e τ ∅ →
    typing Γ 𝟙 e τ ∅ :=
  by
  intros Γ e τ Hclose Hτ
  rw [← List.append_nil Γ]; apply typing.weakening
  rw [escape.nil]; apply typing.escape_strengthened
  induction Γ with
  | nil => apply Hτ
  | cons _ _ IH =>
    apply IH
    apply typing.shrinking; apply Hτ
    apply closed.inc; apply Hclose; omega

theorem preservation.head :
  ∀ Γ e₀ e₁ τ φ,
    head e₀ e₁ →
    lc e₀ →
    typing Γ 𝟙 e₀ τ φ →
    typing Γ 𝟙 e₁ τ φ :=
  by
  intros Γ e₀ e₁ τ φ Hhead Hlc Hτ
  cases Hhead
  case lets Hvalue =>
    cases Hτ
    case lets e v τ φ _ _ Hτv Hclose Hτe =>
      have Hpure : φ = (∅ : Effect) := by cases Hvalue <;> cases Hτv <;> rfl
      rw [Hpure] at Hτv; simp [Hpure]
      rw [← intros.subst]; apply preservation.subst
      apply Hτv; apply Hτe; apply Hclose
  case app₁ Hvalue =>
    cases Hτ
    case app₁ φ Hτv Hτf =>
      cases Hτf
      case fix Hclose _ Hτe =>
        have Hpure : φ = (∅ : Effect) := by cases Hvalue <;> cases Hτv <;> rfl
        rw [Hpure] at Hτv; simp [Hpure]
        admit
  case app₂ =>
    cases Hτ
    case app₂ Hτ₀ Hτ₁ =>
      cases Hτ₀
      case code_fragment Hwbt₀ Hbinds₀ =>
        cases Hτ₁
        case code_fragment Hwbt₁ Hbinds₁ =>
          apply typing.reflect
          rw [← union_pure_right ∅, ← union_pure_right (∅ ∪ ∅)]
          apply typing.app₁
          apply typing.fvar; apply Hbinds₀; apply Hwbt₀
          apply typing.fvar; apply Hbinds₁; apply Hwbt₁
  case lift_lit =>
    cases Hτ
    case lift_lit Hτ =>
      apply typing.reflect
      apply typing.lit
    case lift_fix => contradiction
  case lift_fix e =>
    cases Hτ
    case lift_fix Hτ =>
      cases Hτ
      case fix Hclose Hwbt Hτe =>
        rw [← intros.maping𝕔 Γ.length]
        all_goals admit
    case lift_lit => contradiction
  case fix𝕔 e =>
    cases Hτ
    case fix𝕔 Hwbt Hτ Hclose =>
      apply typing.reflect
      apply typing.fix
      cases Hτ with
      | pure _ _ _ Hτ =>
        generalize Eqe : ({0 ↦ Γ.length + 1}{1 ↦ Γ.length} e) = E
        simp [Eqe] at Hτ
        cases Hτ with
        | code_rep _ _ _ Hτ => apply Hτ
      | reify _ _ _ _ Hτ =>
        generalize Eqe : ({0 ↦ Γ.length + 1}{1 ↦ Γ.length} e) = E
        simp [Eqe] at Hτ
        cases Hτ with
        | code_fragment _ _ _ Hbinds Hwbt =>
          apply typing.fvar
          apply Hbinds; apply Hwbt
      apply Hwbt
      apply Hclose
  case lets𝕔 e =>
    cases Hτ
    case lets𝕔 Hwbt Hτb Hτe Hclose =>
      apply typing.code_rep
      rw [← union_pure_right ∅]
      apply typing.lets
      apply Hτb
      cases Hτe with
      | pure _ _ _ Hτ =>
        generalize Eqe : ({0 ↦ Γ.length} e) = E
        simp [Eqe] at Hτ
        cases Hτ with
        | code_rep _ _ _ Hτ => apply Hτ
      | reify _ _ _ _ Hτ =>
        generalize Eqe : ({0 ↦ Γ.length} e) = E
        simp [Eqe] at Hτ
        cases Hτ with
        | code_fragment _ _ _ Hbinds Hwbt =>
          apply typing.fvar
          apply Hbinds; apply Hwbt
      apply Hwbt
      apply Hclose
  case run =>
    cases Hτ
    case run Hclose Hτ =>
      cases Hτ with
      | pure _ _ _ Hτ =>
        cases Hτ
        case code_rep Hτ =>
          apply typing.escape
          apply Hclose; apply Hτ
      | reify _ _ _ _ Hτ =>
        cases Hτ; contradiction
