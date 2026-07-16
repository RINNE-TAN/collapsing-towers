import Instar.TwoLevelFinal.LogicalEquiv.Compatibility

-- Γ ⊢ e : τ
-- ————————————————
-- Γ ⊧ e ≤𝑙𝑜𝑔 e : τ
theorem log_approx.fundamental :
  ∀ Γ e τ,
    typing Γ 𝟚 e τ ⊥ →
    log_approx Γ e e τ :=
  by
  generalize HEq𝕊 : 𝟚 = 𝕊
  generalize HEqε : ⊥ = ε
  intros Γ e τ Hτ
  revert HEq𝕊 HEqε
  apply @typing.rec
    (fun Γ 𝕊 e τ ε (H : typing Γ 𝕊 e τ ε) =>
      𝟚 = 𝕊 → ⊥ = ε → log_approx Γ e e τ)
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
      by cases ε₀ <;> cases ε₁ <;> cases ε₂ <;> simp at HEqε; simp
    rw [← Hε₀, ← Hε₁] at IH₀
    rw [← Hε₂] at IH₁
    apply compatibility.app₁
    . apply IH₀; apply HEq𝕊; rfl
    . apply IH₁; apply HEq𝕊; rfl
  case lit => apply compatibility.lit
  case binary₁ ε₀ ε₁ _ _ IH₀ IH₁ HEq𝕊 HEqε =>
    have ⟨Hε₀, Hε₁⟩ : ⊥ = ε₀ ∧ ⊥ = ε₁ :=
      by cases ε₀ <;> cases ε₁ <;> simp at HEqε; simp
    rw [← Hε₀] at IH₀
    rw [← Hε₁] at IH₁
    apply compatibility.binary₁
    . apply IH₀; apply HEq𝕊; rfl
    . apply IH₁; apply HEq𝕊; rfl
  case lets ε₀ ε₁ _ _ Hwbt Hclosed IH₀ IH₁ HEq𝕊 HEqε =>
    have ⟨Hε₀, Hε₁⟩ : ⊥ = ε₀ ∧ ⊥ = ε₁ :=
      by cases ε₀ <;> cases ε₁ <;> simp at HEqε; simp
    rw [← Hε₀] at IH₀
    rw [← Hε₁] at IH₁
    rw [← HEq𝕊] at Hwbt IH₁
    apply compatibility.lets
    . apply Hwbt
    . apply Hclosed
    . apply Hclosed
    . apply IH₀; apply HEq𝕊; rfl
    . apply IH₁; rfl; rfl
  case unit => apply compatibility.unit
  case alloc₁ IH HEq𝕊 HEqε =>
    apply compatibility.alloc₁
    apply IH; apply HEq𝕊; apply HEqε
  case load₁ IH HEq𝕊 HEqε =>
    apply compatibility.load₁
    apply IH; apply HEq𝕊; apply HEqε
  case store₁ ε₀ ε₁ _ _ IH₀ IH₁ HEq𝕊 HEqε =>
    have ⟨Hε₀, Hε₁⟩ : ⊥ = ε₀ ∧ ⊥ = ε₁ :=
      by cases ε₀ <;> cases ε₁ <;> simp at HEqε; simp
    rw [← Hε₀] at IH₀
    rw [← Hε₁] at IH₁
    apply compatibility.store₁
    . apply IH₀; apply HEq𝕊; rfl
    . apply IH₁; apply HEq𝕊; rfl
  case fix₁ ε₀ ε₁ ε₂ Hfixε H IH HEq𝕊 HEqε =>
    rw [← HEq𝕊] at H
    have ⟨Hwbt, _⟩ := typing.dynamic_impl_pure _ _ _ _ H
    have ⟨Hε₀, Hε₁⟩ : ⊥ = ε₀ ∧ ⊥ = ε₁ :=
      by simp at Hwbt; simp [Hwbt]
    rw [← Hε₀]
    rw [← Hε₀, ← Hε₁] at IH
    apply compatibility.fix₁
    . apply IH; apply HEq𝕊; apply HEqε
  case ifz₁ ε₀ ε₁ ε₂ _ _ _ IH₀ IH₁ IH₂ HEq𝕊 HEqε =>
    have ⟨Hε₀, Hε₁, Hε₂⟩ : ⊥ = ε₀ ∧ ⊥ = ε₁ ∧ ⊥ = ε₂ :=
      by cases ε₀ <;> cases ε₁ <;> cases ε₂ <;> simp at HEqε; simp
    rw [← Hε₀] at IH₀
    rw [← Hε₁] at IH₁
    rw [← Hε₂] at IH₂
    apply compatibility.ifz₁
    . apply IH₀; apply HEq𝕊; rfl
    . apply IH₁; apply HEq𝕊; rfl
    . apply IH₂; apply HEq𝕊; rfl
  case pure => simp
  case reify => simp
  apply Hτ

theorem log_equiv.fundamental :
  ∀ Γ e τ,
    typing Γ 𝟚 e τ ⊥ →
    log_equiv Γ e e τ :=
  by
  intros Γ e τ Hτ
  constructor
  . apply log_approx.fundamental _ _ _ Hτ
  . apply log_approx.fundamental _ _ _ Hτ
