import Instar.TwoLevelBasic.LogicalEquiv.Compatibility

-- Γ ⊢ e : τ
-- ————————————————
-- Γ ⊧ e ≃𝑙𝑜𝑔 e : τ
theorem log_equiv.fundamental :
  ∀ Γ e τ,
    typing Γ 𝟚 e τ ⊥ →
    log_equiv Γ e e τ :=
  by
  generalize HEq𝕊 : 𝟚 = 𝕊
  generalize HEqε : ⊥ = ε
  intros Γ e τ Hτ
  revert HEq𝕊 HEqε
  apply @typing.rec
    (fun Γ 𝕊 e τ ε (H : typing Γ 𝕊 e τ ε) =>
      𝟚 = 𝕊 → ⊥ = ε → log_equiv Γ e e τ)
    (fun Γ e τ ε (H : typing_reification Γ e τ ε) => true)
  <;> intros
  <;> (try contradiction)
  case fvar Hbinds Hwbt HEq𝕊 _ =>
    rw [← HEq𝕊] at Hbinds Hwbt
    apply compatibility.fvar
    . apply Hbinds
    . apply Hwbt
  case lam H Hwbt Hclosed IH HEq𝕊 _ =>
    rw [← HEq𝕊] at H IH Hwbt
    have ⟨_, HEqε⟩ := typing.dynamic_impl_pure _ _ _ _ H
    rw [HEqε]
    apply compatibility.lam
    . apply Hwbt
    . apply Hclosed
    . apply Hclosed
    . apply IH; rfl; simp [HEqε]
  case app₁ ε₀ ε₁ ε₂ _ _ IH₀ IH₁ HEq𝕊 HEqε =>
    have ⟨Hε₀, Hε₁, Hε₂⟩ : ⊥ = ε₀ ∧ ⊥ = ε₁ ∧ ⊥ = ε₂ :=
      by cases ε₀ <;> cases ε₁ <;> cases ε₂ <;> simp at *
    rw [← Hε₀, ← Hε₁] at IH₀
    rw [← Hε₂] at IH₁
    apply compatibility.app₁
    . apply IH₀; apply HEq𝕊; rfl
    . apply IH₁; apply HEq𝕊; rfl
  case lit => apply compatibility.lit
  case lets ε₀ ε₁ _ _ Hwbt Hclosed IH₀ IH₁ HEq𝕊 HEqε =>
    have ⟨Hε₀, Hε₁⟩ : ⊥ = ε₀ ∧ ⊥ = ε₁ :=
      by cases ε₀ <;> cases ε₁ <;> simp at *
    rw [← Hε₀] at IH₀
    rw [← Hε₁] at IH₁
    rw [← HEq𝕊] at Hwbt IH₁
    apply compatibility.lets
    . apply Hwbt
    . apply Hclosed
    . apply Hclosed
    . apply IH₀; apply HEq𝕊; rfl
    . apply IH₁; rfl; rfl
  case pure => simp
  case reify => simp
  apply Hτ

alias log_equiv.refl := log_equiv.fundamental

lemma log_equiv_value.refl :
  ∀ v τ,
    value v →
    typing ⦰ 𝟚 v τ ⊥ →
    log_equiv_value v v τ :=
  by
  intros v τ Hvalue Hτ
  have ⟨_, _, Hsem_expr⟩ := log_equiv.refl _ _ _ Hτ
  simp only [log_equiv_expr] at Hsem_expr
  have ⟨v₀, v₁, Hstep₀, Hstep₁, Hsem_value⟩ := Hsem_expr _ _ log_equiv_env.nil
  rw [← stepn.value_impl_termination _ _ Hvalue Hstep₀] at Hsem_value
  rw [← stepn.value_impl_termination _ _ Hvalue Hstep₁] at Hsem_value
  apply Hsem_value

lemma log_equiv_env.refl :
  ∀ γ Γ,
    typing.subst γ Γ →
    log_equiv_env γ γ Γ :=
  by
  intros γ Γ HτΓ
  induction HτΓ
  case nil => apply log_equiv_env.nil
  case cons v γ τ Γ Hvalue Hτ _ IH =>
    apply log_equiv_env.cons
    . apply log_equiv_value.refl
      apply Hvalue; apply Hτ
    . apply IH
