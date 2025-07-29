import CollapsingTowers.TwoLvLBasic.Erasure.Erase

-- Γ ⊢ e : τ
-- ————————————————
-- ‖Γ‖ ⊢ ‖e‖ : ‖τ‖
theorem typing.erase_safety : ∀ Γ 𝕊 e τ φ, typing Γ 𝕊 e τ φ → typing ‖Γ‖𝛾 𝟙 ‖e‖ ‖τ‖𝜏 ∅ :=
  by
  intros Γ 𝕊 e τ φ Hτ
  apply
    @typing.rec
      (fun Γ 𝕊 e τ φ (H : typing Γ 𝕊 e τ φ) => typing ‖Γ‖𝛾 𝟙 ‖e‖ ‖τ‖𝜏 ∅)
      (fun Γ e τ φ (H : typing_reification Γ e τ φ) => typing ‖Γ‖𝛾 𝟙 ‖e‖ ‖τ‖𝜏 ∅)
  case fvar =>
    intros _ _ _ _ Hbinds _
    apply typing.fvar
    apply env.erase.binds; apply Hbinds
    apply ty.erase.wbt
  case lam =>
    intros _ _ _ _ _ _ _ HwellBinds Hclose IH
    apply typing.lam
    rw [← env.erase.length, ← comm.erase_opening]
    apply IH
    apply ty.erase.wbt
    rw [← env.erase.length, ← closed.under_erase]
    apply Hclose
  case lift_lam =>
    intros _ _ _ _ _ _ _ IH
    apply IH
  case app₁ =>
    intros _ _ _ _ _ _ _ _ _ _ _ IHf IHarg
    rw [← union_pure_left ∅, ← union_pure_left ∅]
    apply typing.app₁
    apply IHf; apply IHarg
  case app₂ =>
    intros _ _ _ _ _ _ _ _ _ IHf IHarg
    rw [← union_pure_left ∅, ← union_pure_left ∅]
    apply typing.app₁
    apply IHf; apply IHarg
  case lit =>
    intros _ _ _
    apply typing.lit
  case lift_lit =>
    intros _ _ _ _ IH
    apply IH
  case code_fragment =>
    intros _ x _ Hbinds HwellBinds
    apply typing.fvar
    simp; apply env.erase.binds; apply Hbinds
    apply ty.erase.wbt
  case code_rep =>
    intros _ _ _ _ IH
    apply IH
  case reflect =>
    intros _ _ _ _ IH
    apply IH
  case lam𝕔 =>
    intros _ _ _ _ _ _ _ Hclose IH
    apply typing.lam
    rw [← env.erase.length, ← comm.erase_opening]
    apply IH
    apply ty.erase.wbt
    rw [← env.erase.length, ← closed.under_erase]
    apply Hclose
  case lets =>
    intros _ _ _ _ _ _ _ _ _ _ _ Hclose IHb IHe
    rw [← union_pure_left ∅]
    apply typing.lets
    apply IHb
    rw [← env.erase.length, ← comm.erase_opening]
    apply IHe
    apply ty.erase.wbt
    rw [← env.erase.length, ← closed.under_erase]
    apply Hclose
  case lets𝕔 =>
    intros _ _ _ _ _ _ _ _ HwellBinds Hclose IHb IHe
    rw [← union_pure_left ∅]
    apply typing.lets
    apply IHb
    rw [← env.erase.length, ← comm.erase_opening]
    apply IHe
    apply ty.erase.wbt
    rw [← env.erase.length, ← closed.under_erase]
    apply Hclose
  case run =>
    intros _ _ _ _ _ _ IH
    apply IH
  case pure =>
    intros _ _ _ _ IH
    apply IH
  case reify =>
    intros _ _ _ _ _ IH
    apply IH
  apply Hτ

theorem typing_reification.erase_safety : ∀ Γ e τ φ, typing_reification Γ e τ φ → typing_reification ‖Γ‖𝛾 ‖e‖ ‖τ‖𝜏 ∅ :=
  by
  intros Γ e τ φ Hτ
  cases Hτ <;>
  next Hτ =>
    apply typing_reification.pure
    apply typing.erase_safety _ _ _ _ _ Hτ
