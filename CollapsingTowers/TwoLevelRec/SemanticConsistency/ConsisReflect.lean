import CollapsingTowers.TwoLevelRec.LogicalEquiv.Defs
import CollapsingTowers.TwoLevelRec.Erasure.Defs

-- Γ ⊢ E⟦reflect b⟧ : τ
-- ——————————————————————————————————————————————————————
-- ‖Γ‖ ⊨ ‖E⟦reflect b⟧‖ ≈𝑙𝑜𝑔 ‖lets𝕔 x = b in ‖E⟦code x⟧‖ : ‖τ‖
theorem consistency.reflect :
  ∀ Γ E b τ φ,
    ctx𝔼 E →
    typing Γ 𝟙 E⟦.reflect b⟧ τ φ →
    log_equiv ‖Γ‖𝛾 ‖E⟦.reflect b⟧‖ ‖.lets𝕔 b E⟦.code (.bvar 0)⟧‖ ‖τ‖𝜏 :=
  by
  intros Γ E b τ φ HE Hτ₀
  have ⟨τ𝕖, φ₀, φ₁, HEqφ, Hτr₀, HτE₀⟩ := preservation.under_ctx𝔼 _ _ _ _ _ HE Hτ₀
  cases Hτr₀
  case reflect τ𝕖 Hτb₀ =>
    have HτE₀ : typing ((.fragment τ𝕖, 𝟙) :: Γ) 𝟙 E⟦.fvar Γ.length⟧ τ φ₁ :=
      by
      rw [← List.singleton_append, ← union_pure_left φ₁]
      apply HτE₀
      apply typing.fvar
      . simp
      . simp; apply And.left
        apply typing.wbt_pure_at_dyn
        apply Hτb₀
    have HEτ₀ := typing.erase_safety _ _ _ _ _ Hτ₀
    have HEτb₀ := typing.erase_safety _ _ _ _ _ Hτb₀
    have HEτE₀ := typing.erase_safety _ _ _ _ _ HτE₀
    have HEτ₁ : typing ‖Γ‖𝛾 𝟚 ‖.lets𝕔 b E⟦.code (.bvar 0)⟧‖ ‖τ‖𝜏 ∅ :=
      by
      simp; rw [← erase.under_ctx𝔼 _ _ HE]; simp
      rw [← union_pure_left ∅]
      apply typing.lets
      . apply HEτb₀
      . rw [← env.erase.length, ← comm.erase_opening, opening.under_ctx𝔼 _ _ _ _ HE]
        apply HEτE₀
      . apply ty.erase.wbt
      . rw [← env.erase.length, ← closed.under_erase]
        apply closed.under_ctx𝔼 _ _ _ _ HE
        apply typing.closed_at_env; apply Hτ₀; simp
    constructor
    -- left approximation
    . constructor; apply HEτ₀
      constructor; apply HEτ₁
      intros k γ₀ γ₁ HsemΓ
      simp only [log_approx_expr]
      intros j Hindexj v₀ Hvalue₀ Hstep₀
      admit
    -- right approximation
    . constructor; apply HEτ₁
      constructor; apply HEτ₀
      admit
