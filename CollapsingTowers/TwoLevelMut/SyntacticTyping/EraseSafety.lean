import CollapsingTowers.TwoLevelMut.SyntacticTyping.Typing

-- Γ ⊢ e : τ ! φ
-- ——————————————————————
-- ‖Γ‖ ⊢ ‖e‖ : ‖τ‖ ! ‖φ‖
theorem typing.erase.safety :
  ∀ Γ 𝕊 e τ φ,
    typing ϵ Γ 𝕊 e τ φ →
    typing ϵ (erase_env Γ) 𝟚 ‖e‖ (erase_ty τ) (erase_effects φ) :=
  by
  intros Γ 𝕊 e τ φ Hτ
  apply
    @typing.rec ϵ
      (fun Γ 𝕊 e τ φ (H : typing ϵ Γ 𝕊 e τ φ) => typing ϵ (erase_env Γ) 𝟚 ‖e‖ (erase_ty τ) (erase_effects φ))
      (fun Γ e τ φ (H : typing_reification ϵ Γ e τ φ) => typing ϵ (erase_env Γ) 𝟚 ‖e‖ (erase_ty τ) (erase_effects φ))
  <;> intros
  case fvar Hbinds _ =>
    simp; apply typing.fvar
    . apply erase_env.binds; apply Hbinds
    . apply grounded_ty.under_erase
  case lam Hwbt Hclosed IH =>
    simp; apply typing.lam
    . rw [← erase_env.length, ← comm.erase_opening]
      apply IH
    . apply grounded_ty.under_erase
    . rw [← erase_env.length, ← closed.under_erase]
      apply Hclosed
  case lift_lam IH => admit
  case app₁ IHf IHarg => admit
  case app₂ IHf IHarg => admit
  all_goals admit
