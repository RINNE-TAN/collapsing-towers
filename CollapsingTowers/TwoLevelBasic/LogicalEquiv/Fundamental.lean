import CollapsingTowers.TwoLevelBasic.LogicalEquiv.Compatibility

-- Γ ⊢ e : τ
-- ————————————————
-- Γ ⊧ e ≈𝑙𝑜𝑔 e : τ
theorem log_equiv.fundamental :
  ∀ Γ e τ,
    typing Γ 𝟚 e τ ⊥ →
    log_equiv Γ e e τ :=
  by
  generalize HEq𝕊 : 𝟚 = 𝕊
  generalize HEqφ : ⊥ = φ
  intros Γ e τ Hτ
  revert HEq𝕊 HEqφ
  apply @typing.rec
    (fun Γ 𝕊 e τ φ (H : typing Γ 𝕊 e τ φ) =>
      𝟚 = 𝕊 → ⊥ = φ → log_equiv Γ e e τ)
    (fun Γ e τ φ (H : typing_reification Γ e τ φ) => true)
  <;> intros
  <;> (try contradiction)
  case fvar Hbinds Hwbt HEq𝕊 _ =>
    rw [← HEq𝕊] at Hbinds Hwbt
    apply compatibility.fvar
    . apply Hbinds
    . apply Hwbt
  case lam H Hwbt Hclosed IH HEq𝕊 _ =>
    rw [← HEq𝕊] at H IH Hwbt
    have ⟨_, HEqφ⟩ := typing.dynamic_impl_pure _ _ _ _ H
    rw [HEqφ]
    apply compatibility.lam
    . apply Hwbt
    . apply Hclosed
    . apply Hclosed
    . apply IH; rfl; simp [HEqφ]
  case app₁ φ₀ φ₁ φ₂ _ _ IH₀ IH₁ HEq𝕊 HEqφ =>
    have ⟨Hφ₀, Hφ₁, Hφ₂⟩ : ⊥ = φ₀ ∧ ⊥ = φ₁ ∧ ⊥ = φ₂ :=
      by cases φ₀ <;> cases φ₁ <;> cases φ₂ <;> simp at *
    rw [← Hφ₀, ← Hφ₁] at IH₀
    rw [← Hφ₂] at IH₁
    apply compatibility.app₁
    . apply IH₀; apply HEq𝕊; rfl
    . apply IH₁; apply HEq𝕊; rfl
  case lit => apply compatibility.lit
  case lets φ₀ φ₁ _ _ Hwbt Hclosed IH₀ IH₁ HEq𝕊 HEqφ =>
    have ⟨Hφ₀, Hφ₁⟩ : ⊥ = φ₀ ∧ ⊥ = φ₁ :=
      by cases φ₀ <;> cases φ₁ <;> simp at *
    rw [← Hφ₀] at IH₀
    rw [← Hφ₁] at IH₁
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
