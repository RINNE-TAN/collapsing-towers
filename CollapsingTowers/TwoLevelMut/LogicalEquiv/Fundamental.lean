import CollapsingTowers.TwoLevelMut.LogicalEquiv.Compatibility

-- Γ ⊢ e : τ
-- ————————————————
-- Γ ⊧ e ≈𝑙𝑜𝑔 e : τ
theorem log_equiv.fundamental :
  ∀ Γ e τ,
    typing ϵ Γ 𝟚 e τ ⊥ →
    log_equiv Γ e e τ :=
  by
  generalize HEq𝕊 : 𝟚 = 𝕊
  generalize HEqφ : ⊥ = φ
  intros Γ e τ Hτ
  revert HEq𝕊 HEqφ
  apply @typing.rec ϵ
    (fun Γ 𝕊 e τ φ (H : typing ϵ Γ 𝕊 e τ φ) =>
      𝟚 = 𝕊 → ⊥ = φ → log_equiv Γ e e τ)
    (fun Γ e τ φ (H : typing_reification ϵ Γ e τ φ) => true)
  <;> intros
  <;> (try contradiction)
  case fvar Hbinds Hwbt HEq𝕊 _ =>
    rw [← HEq𝕊] at Hbinds Hwbt
    apply compatibility.fvar
    . apply Hbinds
    . apply Hwbt
  case lam H Hwbt Hclosed IH HEq𝕊 _ =>
    rw [← HEq𝕊] at H IH Hwbt
    have ⟨_, HEqφ⟩ := typing.dynamic_impl_pure _ _ _ _ _ H
    rw [HEqφ]
    apply compatibility.lam
    . apply Hwbt
    . apply Hclosed
    . apply Hclosed
    . apply IH; rfl; simp [HEqφ]
  case app₁ φ₀ φ₁ φ₂ _ _ IH₀ IH₁ HEq𝕊 HEqφ =>
    have ⟨Hφ₀, Hφ₁, Hφ₂⟩ : ⊥ = φ₀ ∧ ⊥ = φ₁ ∧ ⊥ = φ₂ :=
      by cases φ₀ <;> cases φ₁ <;> cases φ₂ <;> simp at HEqφ; simp
    rw [← Hφ₀, ← Hφ₁] at IH₀
    rw [← Hφ₂] at IH₁
    apply compatibility.app₁
    . apply IH₀; apply HEq𝕊; rfl
    . apply IH₁; apply HEq𝕊; rfl
  case lit => apply compatibility.lit
  case lets φ₀ φ₁ _ _ Hwbt Hclosed IH₀ IH₁ HEq𝕊 HEqφ =>
    have ⟨Hφ₀, Hφ₁⟩ : ⊥ = φ₀ ∧ ⊥ = φ₁ :=
      by cases φ₀ <;> cases φ₁ <;> simp at HEqφ; simp
    rw [← Hφ₀] at IH₀
    rw [← Hφ₁] at IH₁
    rw [← HEq𝕊] at Hwbt IH₁
    apply compatibility.lets
    . apply Hwbt
    . apply Hclosed
    . apply Hclosed
    . apply IH₀; apply HEq𝕊; rfl
    . apply IH₁; rfl; rfl
  case unit => apply compatibility.unit
  case alloc₁ IH HEq𝕊 HEqφ =>
    apply compatibility.alloc₁
    apply IH; apply HEq𝕊; apply HEqφ
  case load₁ IH HEq𝕊 HEqφ =>
    apply compatibility.load₁
    apply IH; apply HEq𝕊; apply HEqφ
  case store₁ φ₀ φ₁ _ _ IH₀ IH₁ HEq𝕊 HEqφ =>
    have ⟨Hφ₀, Hφ₁⟩ : ⊥ = φ₀ ∧ ⊥ = φ₁ :=
      by cases φ₀ <;> cases φ₁ <;> simp at HEqφ; simp
    rw [← Hφ₀] at IH₀
    rw [← Hφ₁] at IH₁
    apply compatibility.store₁
    . apply IH₀; apply HEq𝕊; rfl
    . apply IH₁; apply HEq𝕊; rfl
  case pure => simp
  case reify => simp
  apply Hτ
