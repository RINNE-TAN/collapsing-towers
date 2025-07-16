
import CollapsingTowers.TwoLevelBasic.SemEquiv.Fundamental
theorem sem_preservation_head :
  ∀ Γ e₀ e₁ τ φ₀ φ₁,
    head𝕄 e₀ e₁ →
    typing Γ .stat e₀ τ φ₀ →
    typing Γ .stat e₁ τ φ₁ →
    sem_equiv_typing (erase_env Γ) (erase e₀) (erase e₁) (erase_ty τ) :=
  by
  intros Γ e₀ e₁ τ φ₀ φ₁ Hhead Hτ₀ Hτ₁
  cases Hhead <;> try apply fundamental; apply Hτ₀
  case lets =>
    intros γ₀ γ₁ HsemΓ
    apply sem_equiv_expr_stepn
    apply fundamental; apply Hτ₁; apply HsemΓ
    . apply pure_stepn.multi; apply pure_stepn.refl
      admit
    . apply pure_stepn.refl
  case app₁ e v Hvalue =>
    intros γ₀ γ₁ HsemΓ
    apply sem_equiv_expr_stepn
    apply fundamental; apply Hτ₁; apply HsemΓ
    . apply pure_stepn.multi; apply pure_stepn.refl
      admit
    . apply pure_stepn.refl
  case lift_lam e =>
    have HEq : erase (.lam𝕔 (map𝕔₀ e)) = erase (.lift (.lam e)) :=
      by simp [erase_maping𝕔]
    rw [HEq]; apply fundamental; apply Hτ₀

theorem sem_preservation_strengthened :
  ∀ Γ e₀ e₁ τ φ,
    step_lvl Γ.length e₀ e₁ →
    typing Γ .stat e₀ τ φ →
    sem_equiv_typing (erase_env Γ) (erase e₀) (erase e₁) (erase_ty τ) :=
  by
  intros Γ e₀ e₁ τ φ
  generalize HEqlvl : Γ.length = lvl
  intros Hstep Hτ
  cases Hstep
  case step𝕄 HM Hlc Hhead𝕄 =>
    induction HM
    case hole =>
      apply sem_preservation_head
      apply Hhead𝕄; apply Hτ
      all_goals admit
    case cons𝔹 => admit
    case consℝ => admit
  case reflect => admit
