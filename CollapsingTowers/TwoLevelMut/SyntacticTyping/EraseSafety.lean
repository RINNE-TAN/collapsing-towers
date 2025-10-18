import CollapsingTowers.TwoLevelMut.SyntacticTyping.Typing

-- Γ ⊢ e : τ ! ω
-- —————————————————————
-- ‖Γ‖ ⊢ ‖e‖ : ‖τ‖ ! ‖ω‖
theorem typing.erase.safety :
  ∀ Γ 𝕊 e τ φ ω,
    typing ϵ Γ 𝕊 e τ φ ω →
    typing ϵ (erase_env Γ) 𝟚 ‖e‖ (erase_ty τ) ⊥ (erase_meffects ω) :=
  by
  intros Γ 𝕊 e τ φ ω Hτ
  apply
    @typing.rec ϵ
      (fun Γ 𝕊 e τ φ ω (H : typing ϵ Γ 𝕊 e τ φ ω) => typing ϵ (erase_env Γ) 𝟚 ‖e‖ (erase_ty τ) ⊥ (erase_meffects ω))
      (fun Γ e τ φ ω (H : typing_reification ϵ Γ e τ φ ω) => typing ϵ (erase_env Γ) 𝟚 ‖e‖ (erase_ty τ) ⊥ (erase_meffects ω))
  <;> intros
  <;> try simp only [erase_meffects.union, erase_meffects.empty]
  case fvar Hbinds _ =>
    apply typing.fvar
    . apply erase_env.binds; apply Hbinds
    . apply grounded_ty.under_erase
  case lam Hwbt Hclosed IH =>
    apply typing.lam
    . rw [← erase_env.length, ← comm.erase_opening]
      apply IH
    . apply grounded_ty.under_erase
    . rw [← erase_env.length, ← closed.under_erase]
      apply Hclosed
  case lift_lam IH => apply IH
  case app₁ IHf IHarg =>
    rw [← REffects.union_pure ⊥, ← REffects.union_pure (⊥ ∪ ⊥)]
    apply typing.app₁
    . apply IHf
    . apply IHarg
  case app₂ IHf IHarg =>
    rw [← REffects.union_pure ⊥, ← REffects.union_pure (⊥ ∪ ⊥)]
    apply typing.app₁
    . apply IHf
    . apply IHarg
  case lit => apply typing.lit
  case lift_lit IH => apply IH
  case code_fragment x _ Hbinds Hwbt =>
    apply typing.fvar
    . simp; apply erase_env.binds; apply Hbinds
    . apply grounded_ty.under_erase
  case code_rep IH => apply IH
  case reflect IH => apply IH
  case lam𝕔 Hclosed _ IH =>
    apply typing.lam
    . rw [← erase_env.length, ← comm.erase_opening]
      apply IH
    . apply grounded_ty.under_erase
    . rw [← erase_env.length, ← closed.under_erase]
      apply Hclosed
  case lets Hclosed IHb IHe =>
    rw [← REffects.union_pure ⊥]
    apply typing.lets
    . apply IHb
    . rw [← erase_env.length, ← comm.erase_opening]
      apply IHe
    . apply grounded_ty.under_erase
    . rw [← erase_env.length, ← closed.under_erase]
      apply Hclosed
  case lets𝕔 Hclosed IHb IHe =>
    rw [← REffects.union_pure ⊥]
    apply typing.lets
    . apply IHb
    . rw [← erase_env.length, ← comm.erase_opening]
      apply IHe
    . apply grounded_ty.under_erase
    . rw [← erase_env.length, ← closed.under_erase]
      apply Hclosed
  case run IH =>
    rw [erase_meffects.cancel_escape]
    apply IH
  case unit => apply typing.unit
  case lift_unit IH => apply IH
  case loc => contradiction
  case alloc₁ IH =>
    rw [erase_meffects.init]
    apply typing.alloc₁; apply IH
  case alloc₂ IH =>
    rw [erase_meffects.init]
    apply typing.alloc₁; apply IH
  case load₁ IH =>
    rw [erase_meffects.read]
    apply typing.load₁; apply IH
  case load₂ IH =>
    rw [erase_meffects.read]
    apply typing.load₁; apply IH
  case store₁ IHl IHr =>
    rw [← REffects.union_pure ⊥]
    rw [erase_meffects.write]
    apply typing.store₁
    . apply IHl
    . apply IHr
  case store₂ IHl IHr =>
    rw [← REffects.union_pure ⊥]
    rw [erase_meffects.write]
    apply typing.store₁
    . apply IHl
    . apply IHr
  case pure IH => apply IH
  case reify IH => apply IH
  apply Hτ
