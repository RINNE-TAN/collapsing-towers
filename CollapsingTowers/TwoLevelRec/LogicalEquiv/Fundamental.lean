import CollapsingTowers.TwoLevelRec.LogicalEquiv.Compatibility

-- 𝔾(e₀)
-- Γ ⊢ e : τ
-- ————————————————
-- Γ ⊧ e ≤𝑙𝑜𝑔 e : τ
theorem typing.fundamental :
  ∀ Γ e τ,
    typing Γ 𝟙 e τ ∅ → grounded e →
    log_rel_typing Γ e e τ :=
  by
  generalize HEq𝕊 : 𝟙 = 𝕊
  generalize HEqφ : ∅ = φ
  intros Γ e τ Hτ
  revert HEq𝕊 HEqφ
  apply
    @typing.rec
      (fun Γ 𝕊 e τ φ (H : typing Γ 𝕊 e τ φ) =>
        𝟙 = 𝕊 → ∅ = φ → grounded e → log_rel_typing Γ e e τ)
      (fun Γ e τ φ (H : typing_reification Γ e τ φ) =>
        ∅ = φ → grounded e → log_rel_typing Γ e e τ)
  <;> intros
  case fvar HBinds Hwbt HEq𝕊 HEqφ HG =>
    apply compatibility.fvar
    rw [HEq𝕊]; apply HBinds
    rw [HEq𝕊]; apply Hwbt
  case lam HG HEq𝕊 HEqφ =>
    admit
  all_goals admit
