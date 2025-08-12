import CollapsingTowers.TwoLevelRec.Erasure.Erase

-- Γ ⊢ e : τ
-- ————————————————
-- ‖Γ‖ ⊢ ‖e‖ : ‖τ‖
theorem typing.erase_safety : ∀ Γ 𝕊 e τ φ, typing Γ 𝕊 e τ φ → typing ‖Γ‖𝛾 𝟚 ‖e‖ ‖τ‖𝜏 ∅ :=
  by
  intros Γ 𝕊 e τ φ Hτ
  apply
    @typing.rec
      (fun Γ 𝕊 e τ φ (H : typing Γ 𝕊 e τ φ) => typing ‖Γ‖𝛾 𝟚 ‖e‖ ‖τ‖𝜏 ∅)
      (fun Γ e τ φ (H : typing_reification Γ e τ φ) => typing ‖Γ‖𝛾 𝟚 ‖e‖ ‖τ‖𝜏 ∅)
  <;> intros
  case fvar Hbinds _ =>
    apply typing.fvar
    apply env.erase.binds; apply Hbinds
    apply ty.erase.wbt
  case lam Hwbt Hclose IH =>
    apply typing.lam
    rw [← env.erase.length, ← comm.erase_opening]
    apply IH
    apply ty.erase.wbt
    rw [← env.erase.length, ← closed.under_erase]
    apply Hclose
  case lift_lam IH =>
    apply IH
  case app₁ IHf IHarg =>
    rw [← union_pure_left ∅, ← union_pure_left ∅]
    apply typing.app₁
    apply IHf; apply IHarg
  case app₂ IHf IHarg =>
    rw [← union_pure_left ∅, ← union_pure_left ∅]
    apply typing.app₁
    apply IHf; apply IHarg
  case lit =>
    apply typing.lit
  case lift_lit IH =>
    apply IH
  case code_fragment x _ Hbinds Hwbt =>
    apply typing.fvar
    simp; apply env.erase.binds; apply Hbinds
    apply ty.erase.wbt
  case code_rep IH =>
    apply IH
  case reflect IH =>
    apply IH
  case lam𝕔 Hclose IH =>
    apply typing.lam
    rw [← env.erase.length, ← comm.erase_opening]
    apply IH
    apply ty.erase.wbt
    rw [← env.erase.length, ← closed.under_erase]
    apply Hclose
  case lets Hclose IHb IHe =>
    rw [← union_pure_left ∅]
    apply typing.lets
    apply IHb
    rw [← env.erase.length, ← comm.erase_opening]
    apply IHe
    apply ty.erase.wbt
    rw [← env.erase.length, ← closed.under_erase]
    apply Hclose
  case lets𝕔 Hwbt Hclose IHb IHe =>
    rw [← union_pure_left ∅]
    apply typing.lets
    apply IHb
    rw [← env.erase.length, ← comm.erase_opening]
    apply IHe
    apply ty.erase.wbt
    rw [← env.erase.length, ← closed.under_erase]
    apply Hclose
  case run IH =>
    apply IH
  case fix₁ IH =>
    apply typing.fix₁
    simp; rfl; apply IH
  case fix₂ IH =>
    apply typing.fix₁
    simp; rfl; apply IH
  case pure IH =>
    apply IH
  case reify IH=>
    apply IH
  apply Hτ
