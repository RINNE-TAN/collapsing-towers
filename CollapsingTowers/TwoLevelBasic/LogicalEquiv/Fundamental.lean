import CollapsingTowers.TwoLevelBasic.LogicalEquiv.Compatibility
import CollapsingTowers.TwoLevelBasic.Erasure.Defs

-- Γ ⊢ e : τ
-- —————————————————————
-- ‖Γ‖ ⊧ ‖e‖ ≈ ‖e‖ : ‖τ‖
theorem typing.erase.fundamental :
  ∀ Γ 𝕊 e τ φ,
    typing Γ 𝕊 e τ φ →
    log_equiv_typing ‖Γ‖𝛾 ‖e‖ ‖e‖ ‖τ‖𝜏 :=
  by
  intros Γ 𝕊 e τ φ Hτ
  apply
    @typing.rec
      (fun Γ 𝕊 e τ φ (H : typing Γ 𝕊 e τ φ) =>
          log_equiv_typing ‖Γ‖𝛾 ‖e‖ ‖e‖ ‖τ‖𝜏)
      (fun Γ e τ φ (H : typing_reification Γ e τ φ) =>
          log_equiv_typing ‖Γ‖𝛾 ‖e‖ ‖e‖ ‖τ‖𝜏)
  case fvar =>
    intros _ _ _ _ Hbinds _
    apply compatibility.fvar
    apply env.erase.binds; apply Hbinds
  case lam =>
    intros _ _ _ _ _ _ H _ Hclose IH
    apply compatibility.lam
    simp [← env.erase.length, ← closed.under_erase]; apply Hclose
    simp [← env.erase.length, ← closed.under_erase]; apply Hclose
    rw [← env.erase.length, ← comm.erase_opening]
    apply IH
  case lift_lam =>
    intros _ _ _ _ _ _ _ IH
    apply IH
  case app₁ =>
    intros _ _ _ _ _ _ _ _ _ Hf Harg IHf IHarg
    apply compatibility.app
    apply IHf; apply IHarg
  case app₂ =>
    intros _ _ _ _ _ _ _ _ _ IHf IHarg
    apply compatibility.app
    apply IHf; apply IHarg
  case lit =>
    intros _ _ n
    apply compatibility.lit
  case lift_lit =>
    intros _ _ _ _ IH
    apply IH
  case code_fragment =>
    intros _ x _ Hbinds _
    apply compatibility.fvar; simp
    apply env.erase.binds; apply Hbinds
  case code_rep =>
    intros _ _ _ _ IH
    apply IH
  case reflect =>
    intros _ _ _ _ IH
    apply IH
  case lam𝕔 =>
    intros _ _ _ _ _ H _ Hclose IH
    apply compatibility.lam
    simp [← env.erase.length, ← closed.under_erase]; apply Hclose
    simp [← env.erase.length, ← closed.under_erase]; apply Hclose
    rw [← env.erase.length, ← comm.erase_opening]
    apply IH
  case lets =>
    intros _ _ _ _ _ _ _ _ Hb He _ Hclose IHb IHe
    apply compatibility.lets
    constructor
    . simp [← env.erase.length, ← closed.under_erase]; apply typing.closed_at_env; apply Hb
    . simp [← env.erase.length, ← closed.under_erase]; apply Hclose
    constructor
    . simp [← env.erase.length, ← closed.under_erase]; apply typing.closed_at_env; apply Hb
    . simp [← env.erase.length, ← closed.under_erase]; apply Hclose
    apply IHb
    rw [← env.erase.length, ← comm.erase_opening]
    apply IHe
  case lets𝕔 =>
    intros _ _ _ _ _ _ Hb He _ Hclose IHb IHe
    apply compatibility.lets
    constructor
    . simp [← env.erase.length, ← closed.under_erase]; apply typing.closed_at_env; apply Hb
    . simp [← env.erase.length, ← closed.under_erase]; apply Hclose
    constructor
    . simp [← env.erase.length, ← closed.under_erase]; apply typing.closed_at_env; apply Hb
    . simp [← env.erase.length, ← closed.under_erase]; apply Hclose
    apply IHb
    rw [← env.erase.length, ← comm.erase_opening]
    apply IHe
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

theorem typing_reification.erase.fundamental :
  ∀ Γ e τ φ,
    typing_reification Γ e τ φ →
    log_equiv_typing ‖Γ‖𝛾 ‖e‖ ‖e‖ ‖τ‖𝜏 :=
  by
  intros Γ e τ φ Hτ
  cases Hτ
  all_goals
  next Hτ =>
    apply typing.erase.fundamental _ _ _ _ _ Hτ

theorem typing.fundamental :
  ∀ Γ 𝕊 e τ φ,
    typing ‖Γ‖𝛾 𝕊 ‖e‖ ‖τ‖𝜏 φ →
    log_equiv_typing ‖Γ‖𝛾 ‖e‖ ‖e‖ ‖τ‖𝜏 :=
  by
  intros Γ 𝕊 e τ φ Hτ
  rw [← identity.env.erase_erase, ← identity.erase_erase, ← identity.ty.erase_erase]
  apply typing.erase.fundamental; apply Hτ
