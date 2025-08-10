import CollapsingTowers.TwoLevelRec.LogicEquiv.Compatibility
import CollapsingTowers.TwoLevelRec.Erasure.Defs

-- Γ ⊢ e : τ
-- —————————————————————
-- ‖Γ‖ ⊧ ‖e‖ ≈ ‖e‖ : ‖τ‖
theorem typing.erase.fundamental :
  ∀ Γ 𝕊 e τ φ,
    typing Γ 𝕊 e τ φ →
    logic_rel_typing ‖Γ‖𝛾 ‖e‖ ‖e‖ ‖τ‖𝜏 :=
  by
  intros Γ 𝕊 e τ φ Hτ
  apply
    @typing.rec
      (fun Γ 𝕊 e τ φ (H : typing Γ 𝕊 e τ φ) =>
          logic_rel_typing ‖Γ‖𝛾 ‖e‖ ‖e‖ ‖τ‖𝜏)
      (fun Γ e τ φ (H : typing_reification Γ e τ φ) =>
          logic_rel_typing ‖Γ‖𝛾 ‖e‖ ‖e‖ ‖τ‖𝜏)
  <;> intros
  case fvar Hbinds Hwbt =>
    apply compatibility.fvar
    apply env.erase.binds; apply Hbinds
    apply ty.erase.wbt
  case lam H _ Hclose IH =>
    apply compatibility.lam; apply ty.erase.wbt
    simp [← env.erase.length, ← closed.under_erase]; apply Hclose
    simp [← env.erase.length, ← closed.under_erase]; apply Hclose
    rw [← env.erase.length, ← comm.erase_opening]
    apply IH
  case lift_lam IH =>
    apply IH
  case app₁ IHf IHarg =>
    apply compatibility.app₁
    apply IHf; apply IHarg
  case app₂ IHf IHarg =>
    apply compatibility.app₁
    apply IHf; apply IHarg
  case lit =>
    apply compatibility.lit
  case lift_lit IH =>
    apply IH
  case code_fragment x _ Hbinds _ =>
    apply compatibility.fvar; simp
    apply env.erase.binds; apply Hbinds
    apply ty.erase.wbt
  case code_rep IH =>
    apply IH
  case reflect IH =>
    apply IH
  case lam𝕔 Hclose IH =>
    apply compatibility.lam;apply ty.erase.wbt
    simp [← env.erase.length, ← closed.under_erase]; apply Hclose
    simp [← env.erase.length, ← closed.under_erase]; apply Hclose
    rw [← env.erase.length, ← comm.erase_opening]
    apply IH
  case lets τ𝕒 τ𝕓 _ _ Hb He _ Hclose IHb IHe =>
    apply compatibility.lets; apply ty.erase.wbt _ τ𝕒
    simp [← env.erase.length, ← closed.under_erase]; apply Hclose
    simp [← env.erase.length, ← closed.under_erase]; apply Hclose
    apply IHb
    rw [← env.erase.length, ← comm.erase_opening]
    apply IHe
  case lets𝕔 τ𝕒 τ𝕓 _ Hb He _ Hclose IHb IHe =>
    apply compatibility.lets; apply ty.erase.wbt _ τ𝕒
    simp [← env.erase.length, ← closed.under_erase]; apply Hclose
    simp [← env.erase.length, ← closed.under_erase]; apply Hclose
    apply IHb
    rw [← env.erase.length, ← comm.erase_opening]
    apply IHe
  case fix₁ IH =>
    apply compatibility.fix₁
    apply IH
  case fix₂ IH =>
    apply compatibility.fix₁
    apply IH
  case run IH =>
    apply IH
  case pure IH =>
    apply IH
  case reify IH =>
    apply IH
  apply Hτ

theorem typing_reification.erase.fundamental :
  ∀ Γ e τ φ,
    typing_reification Γ e τ φ →
    logic_rel_typing ‖Γ‖𝛾 ‖e‖ ‖e‖ ‖τ‖𝜏 :=
  by
  intros Γ e τ φ Hτ
  cases Hτ
  all_goals
  next Hτ =>
    apply typing.erase.fundamental _ _ _ _ _ Hτ

theorem typing.fundamental :
  ∀ Γ 𝕊 e τ φ,
    typing ‖Γ‖𝛾 𝕊 ‖e‖ ‖τ‖𝜏 φ →
    logic_rel_typing ‖Γ‖𝛾 ‖e‖ ‖e‖ ‖τ‖𝜏 :=
  by
  intros Γ 𝕊 e τ φ Hτ
  rw [← identity.env.erase_erase, ← identity.erase_erase, ← identity.ty.erase_erase]
  apply typing.erase.fundamental; apply Hτ
