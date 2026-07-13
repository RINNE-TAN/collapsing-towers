import Instar.TwoLevelMut.SyntacticTyping.Typing

-- Γ ⊢ e : τ
-- ————————————————
-- ‖Γ‖ ⊢ ‖e‖ : ‖τ‖
theorem typing.erase.safety :
  ∀ Γ 𝕊 e τ ε,
    typing Γ 𝕊 e τ ε →
    typing (erase_env Γ) 𝟚 ‖e‖ (erase_ty τ) ⊥ :=
  by
  intros Γ 𝕊 e τ ε Hτ
  apply
    @typing.rec
      (fun Γ 𝕊 e τ ε (H : typing Γ 𝕊 e τ ε) => typing (erase_env Γ) 𝟚 ‖e‖ (erase_ty τ) ⊥)
      (fun Γ e τ ε (H : typing_reification Γ e τ ε) => typing (erase_env Γ) 𝟚 ‖e‖ (erase_ty τ) ⊥)
  <;> intros
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
    rw [← Effect.union_pure ⊥, ← Effect.union_pure (⊥ ∪ ⊥)]
    apply typing.app₁
    . apply IHf
    . apply IHarg
  case app₂ IHf IHarg =>
    rw [← Effect.union_pure ⊥, ← Effect.union_pure (⊥ ∪ ⊥)]
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
  case lam𝕔 Hclosed IH =>
    apply typing.lam
    . rw [← erase_env.length, ← comm.erase_opening]
      apply IH
    . apply grounded_ty.under_erase
    . rw [← erase_env.length, ← closed.under_erase]
      apply Hclosed
  case lets Hclosed IHb IHe =>
    rw [← Effect.union_pure ⊥]
    apply typing.lets
    . apply IHb
    . rw [← erase_env.length, ← comm.erase_opening]
      apply IHe
    . apply grounded_ty.under_erase
    . rw [← erase_env.length, ← closed.under_erase]
      apply Hclosed
  case lets𝕔 Hclosed IHb IHe =>
    rw [← Effect.union_pure ⊥]
    apply typing.lets
    . apply IHb
    . rw [← erase_env.length, ← comm.erase_opening]
      apply IHe
    . apply grounded_ty.under_erase
    . rw [← erase_env.length, ← closed.under_erase]
      apply Hclosed
  case run IH => apply IH
  case unit => apply typing.unit
  case lift_unit IH => apply IH
  case alloc₁ IH => apply typing.alloc₁; apply IH
  case alloc₂ IH => apply typing.alloc₁; apply IH
  case load₁ IH => apply typing.load₁; apply IH
  case load₂ IH => apply typing.load₁; apply IH
  case store₁ IHl IHr =>
    rw [← Effect.union_pure ⊥]
    apply typing.store₁
    . apply IHl
    . apply IHr
  case store₂ IHl IHr =>
    rw [← Effect.union_pure ⊥]
    apply typing.store₁
    . apply IHl
    . apply IHr
  case pure IH => apply IH
  case reify IH => apply IH
  apply Hτ

theorem typing_reification.erase.safety :
  ∀ Γ e τ ε,
    typing_reification Γ e τ ε →
    typing (erase_env Γ) 𝟚 ‖e‖ (erase_ty τ) ⊥ :=
  by
  intros Γ e τ ε Hτ
  cases Hτ
  all_goals next Hτ =>
    apply typing.erase.safety _ _ _ _ _ Hτ
