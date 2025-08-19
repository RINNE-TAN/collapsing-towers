import CollapsingTowers.TwoLevelRec.SyntacticTyping.Typing

-- Γ ⊢ e : τ
-- ————————————————
-- ‖Γ‖ ⊢ ‖e‖ : ‖τ‖
theorem typing.erase_safety : ∀ Γ 𝕊 e τ φ, typing Γ 𝕊 e τ φ → typing (erase_env Γ) 𝟙 ‖e‖ (erase_ty τ) ⊥ :=
  by
  intros Γ 𝕊 e τ φ Hτ
  apply
    @typing.rec
      (fun Γ 𝕊 e τ φ (H : typing Γ 𝕊 e τ φ) => typing (erase_env Γ) 𝟙 ‖e‖ (erase_ty τ) ⊥)
      (fun Γ e τ φ (H : typing_reification Γ e τ φ) => typing (erase_env Γ) 𝟙 ‖e‖ (erase_ty τ) ⊥)
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
  case binary₁ IHl IHr =>
    rw [← Effect.union_pure ⊥]
    apply typing.binary₁
    . apply IHl
    . apply IHr
  case binary₂ IHl IHr =>
    rw [← Effect.union_pure ⊥]
    apply typing.binary₁
    . apply IHl
    . apply IHr
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
  case fix₁ IH =>
    apply typing.fix₁
    . simp; rfl
    . apply IH
  case fix₂ IH =>
    apply typing.fix₁
    . simp; rfl
    . apply IH
  case ifz₁ IHc IHl IHr =>
    rw [← Effect.union_pure ⊥, ← Effect.union_pure (⊥ ∪ ⊥)]
    apply typing.ifz₁
    . apply IHc
    . apply IHl
    . apply IHr
  case ifz₂ IHc IHl IHr =>
    rw [← Effect.union_pure ⊥, ← Effect.union_pure (⊥ ∪ ⊥)]
    apply typing.ifz₁
    . apply IHc
    . apply IHl
    . apply IHr
  case pure IH => apply IH
  case reify IH => apply IH
  apply Hτ
