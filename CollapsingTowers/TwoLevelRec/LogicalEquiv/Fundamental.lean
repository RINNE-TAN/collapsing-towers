import CollapsingTowers.TwoLevelRec.LogicalEquiv.Compatibility

-- Γ ⊢ e : τ
-- ————————————————
-- Γ ⊧ e ≤𝑙𝑜𝑔 e : τ
theorem log_rel_typing.fundamental :
  ∀ Γ e τ,
    typing Γ 𝟚 e τ ∅ →
    log_rel_typing Γ e e τ :=
  by
  generalize HEq𝕊 : 𝟚 = 𝕊
  generalize HEqφ : ∅ = φ
  intros Γ e τ Hτ
  revert HEq𝕊 HEqφ
  apply @typing.rec
    (fun Γ 𝕊 e τ φ (H : typing Γ 𝕊 e τ φ) =>
      𝟚 = 𝕊 → ∅ = φ → log_rel_typing Γ e e τ)
    (fun Γ e τ φ (H : typing_reification Γ e τ φ) => true)
  <;> intros
  <;> (try contradiction)
  case fvar HBinds Hwbt HEq𝕊 _ =>
    rw [← HEq𝕊] at HBinds Hwbt
    apply compatibility.fvar
    . apply HBinds
    . apply Hwbt
  case lam H Hwbt Hclosed IH HEq𝕊 _ =>
    rw [← HEq𝕊] at H IH Hwbt
    have ⟨_, HEqφ⟩ := typing.wbt_pure_at_dyn _ _ _ _ H
    rw [HEqφ]
    apply compatibility.lam
    . apply Hwbt
    . apply Hclosed
    . apply Hclosed
    . apply IH; rfl; simp [HEqφ]
  case app₁ φ₀ φ₁ φ₂ _ _ IH₀ IH₁ HEq𝕊 HEqφ =>
    have ⟨Hφ₀, Hφ₁, Hφ₂⟩ : ∅ = φ₀ ∧ ∅ = φ₁ ∧ ∅ = φ₂ :=
      by cases φ₀ <;> cases φ₁ <;> cases φ₂ <;> simp at *
    rw [← Hφ₀, ← Hφ₁] at IH₀
    rw [← Hφ₂] at IH₁
    apply compatibility.app₁
    . apply IH₀; apply HEq𝕊; rfl
    . apply IH₁; apply HEq𝕊; rfl
  case lit => apply compatibility.lit
  case lets φ₀ φ₁ _ _ Hwbt Hclosed IH₀ IH₁ HEq𝕊 HEqφ =>
    have ⟨Hφ₀, Hφ₁⟩ : ∅ = φ₀ ∧ ∅ = φ₁ :=
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
  case fix₁ φ₀ φ₁ φ₂ Hfixφ H IH HEq𝕊 HEqφ =>
    rw [← HEq𝕊] at H
    have ⟨Hwbt, _⟩ := typing.wbt_pure_at_dyn _ _ _ _ H
    have ⟨Hφ₀, Hφ₁⟩ : ∅ = φ₀ ∧ ∅ = φ₁ :=
      by simp at Hwbt; simp [Hwbt]
    rw [← Hφ₀]
    rw [← Hφ₀, ← Hφ₁] at IH
    apply compatibility.fix₁
    . apply IH; apply HEq𝕊; apply HEqφ
  case pure => simp
  case reify => simp
  apply Hτ

lemma log_rel_value.fundamental :
  ∀ k v τ,
    value v →
    typing [] 𝟚 v τ ∅ →
    log_rel_value k v v τ :=
  by
  intros k v τ Hvalue Hτ
  cases k
  case zero =>
    have ⟨Hwbt, _⟩ := typing.wbt_pure_at_dyn _ _ _ _ Hτ
    cases Hvalue
    case lam e _ =>
      cases τ
      case arrow τ𝕒 τ𝕓 φ =>
        cases φ <;> simp at Hwbt
        simp only [log_rel_value]
        constructor; apply Hτ
        constructor; apply Hτ
        simp
      all_goals contradiction
    case lit n =>
      cases τ <;> try contradiction
      simp
    case code => nomatch Hτ
  case succ k =>
    have ⟨_, _, Hsem_expr⟩ := log_rel_typing.fundamental _ _ _ Hτ
    simp only [log_rel_expr] at Hsem_expr
    have ⟨r, Hstep, Hsem_value⟩ := Hsem_expr (k + 1) _ _ (log_rel_env.nil _) 0 (by omega) _ Hvalue (stepn_indexed.refl _)
    rw [← stepn.value_impl_termination _ _ Hvalue Hstep] at Hsem_value
    apply Hsem_value

lemma log_rel_env.fundamental :
  ∀ k γ Γ,
    typing.subst γ Γ →
    log_rel_env k γ γ Γ :=
  by
  intros k γ Γ HτΓ
  induction HτΓ
  case nil => apply log_rel_env.nil
  case cons v γ τ Γ Hvalue Hτ _ IH =>
    apply log_rel_env.cons
    . apply log_rel_value.fundamental
      apply Hvalue; apply Hτ
    . apply IH
