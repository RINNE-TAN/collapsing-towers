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
    simp
    apply typing.fvar
    . apply erase_env.binds; apply Hbinds
    . apply grounded_ty.under_erase
  case lam Hwbt Hclosed IH =>
    simp
    apply typing.lam
    . rw [← erase_env.length, ← comm.erase_opening]
      apply IH
    . apply grounded_ty.under_erase
    . rw [← erase_env.length, ← closed.under_erase]
      apply Hclosed
  case lift_lam Hφ IH =>
    simp only [erase_effects.union]
    simp [-erase_effects]
    apply IH
  case app₁ IHf IHarg =>
    simp only [erase_effects.union]
    apply typing.app₁
    . apply IHf
    . apply IHarg
  case app₂ IHf IHarg =>
    simp only [erase_effects.union]
    simp [-erase_effects]
    apply typing.app₁
    . apply IHf
    . apply IHarg
  case lit =>
    simp
    apply typing.lit
  case lift_lit IH =>
    simp only [erase_effects.union]
    simp [-erase_effects]
    apply IH
  case code_fragment Hbinds _ =>
    simp
    apply typing.fvar
    . apply erase_env.binds; apply Hbinds
    . apply grounded_ty.under_erase
  case code_rep IH => apply IH
  case reflect IH =>
    simp only [erase_effects.union]
    simp [-erase_effects]
    apply IH
  case lam𝕔 Hclose _ IH =>
    simp [-erase_effects]
    apply typing.lam
    . rw [← erase_env.length, ← comm.erase_opening]
      apply IH
    . apply grounded_ty.under_erase
    . rw [← erase_env.length, ← closed.under_erase]
      apply Hclose
  case lets Hclose IHb IHe =>
    simp only [erase_effects.union]
    apply typing.lets
    . apply IHb
    . rw [← erase_env.length, ← comm.erase_opening]
      apply IHe
    . apply grounded_ty.under_erase
    . rw [← erase_env.length, ← closed.under_erase]
      apply Hclose
  case lets𝕔 Hclose IHb IHe =>
    simp [-erase_effects]
    rw [← Set.empty_union (erase_effects _)]
    apply typing.lets
    . simp at IHb; apply IHb
    . rw [← erase_env.length, ← comm.erase_opening]
      apply IHe
    . apply grounded_ty.under_erase
    . rw [← erase_env.length, ← closed.under_erase]
      apply Hclose
  case run IH =>
    simp only [erase_effects.diff_reify, erase_effects.escape]
    apply IH
  case unit =>
    simp
    apply typing.unit
  case lift_unit IH =>
    simp only [erase_effects.union]
    simp [-erase_effects]
    apply IH
  case loc => contradiction
  case alloc₁ IH =>
    simp only [erase_effects.union, erase_effects.mutate]
    apply typing.alloc₁
    apply IH
  case alloc₂ IH =>
    simp only [erase_effects.union, erase_effects.mutate, erase_effects.reify, Set.union_empty]
    apply typing.alloc₁
    apply IH
  case load₁ IH =>
    simp only [erase_effects.union, erase_effects.mutate]
    apply typing.load₁
    apply IH
  case load₂ IH =>
    simp only [erase_effects.union, erase_effects.mutate, erase_effects.reify, Set.union_empty]
    apply typing.load₁
    apply IH
  case store₁ IHl IHr =>
    simp only [erase_effects.union, erase_effects.mutate]
    apply typing.store₁
    . apply IHl
    . apply IHr
  case store₂ IHl IHr =>
    simp only [erase_effects.union, erase_effects.mutate, erase_effects.reify, Set.union_empty]
    apply typing.store₁
    . apply IHl
    . apply IHr
  case pure IH => apply IH
  case reify IH => apply IH
  apply Hτ
