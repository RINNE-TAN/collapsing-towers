import CollapsingTowers.TwoLevelMut.SyntacticTyping.Defs
import CollapsingTowers.TwoLevelMut.OperationalSemantics.Defs

@[simp]
def dyn_env (Γ : TEnv) : Prop :=
  ∀ x τ 𝕊, binds x (τ, 𝕊) Γ → 𝕊 = 𝟚

lemma dyn_env.extend :
  ∀ Γ τ,
    dyn_env Γ →
    dyn_env ((τ, 𝟚) :: Γ) :=
  by
  intros Γ τ₀ HDyn x τ₁ 𝕊 Hbinds
  by_cases HEq : Γ.length = x
  . simp [if_pos HEq] at Hbinds
    simp [Hbinds]
  . simp [if_neg HEq] at Hbinds
    apply HDyn; apply Hbinds

theorem progress.strengthened :
  ∀ σ₀ Γ e₀ τ φ,
    ok σ₀ →
    typing_reification σ₀ Γ e₀ τ φ →
    dyn_env Γ →
    (∃ σ₁ e₁, step_lvl Γ.length ⟨σ₀, e₀⟩ ⟨σ₁, e₁⟩) ∨ value e₀ :=
  by
  intros σ₀ Γ e₀ τ φ Hok Hτ
  revert Hok
  apply @typing_reification.rec σ₀
    (fun Γ 𝕊 e₀ τ φ (H : typing σ₀ Γ 𝕊 e₀ τ φ) =>
      ok σ₀ → dyn_env Γ → 𝕊 = 𝟙 → (∃ σ₁ e₁, step_lvl Γ.length ⟨σ₀, e₀⟩ ⟨σ₁, e₁⟩) ∨ value e₀)
    (fun Γ e₀ τ φ (H : typing_reification σ₀ Γ e₀ τ φ) =>
      ok σ₀ → dyn_env Γ → (∃ σ₁ e₁, step_lvl Γ.length ⟨σ₀, e₀⟩ ⟨σ₁, e₁⟩) ∨ value e₀)
  <;> intros
  case fvar x _ Hbinds Hwbt Hok HDyn HEq𝕊 => simp [HDyn _ _ _ Hbinds] at HEq𝕊
  case lam H Hwbt Hclosed IH Hok HDyn HEq𝕊 => right; apply value.lam; simp; rw [← lc.under_opening]; apply typing.regular _ _ _ _ _ _ H
  case lit => right; apply value.lit
  case code_fragment => right; apply value.code; simp
  case code_rep H IH Hok HDyn HEq𝕊 => right; apply value.code; apply typing.regular _ _ _ _ _ _ H
  case lift_lam H IH Hok HDyn HEq𝕊 => admit
  all_goals admit

theorem progress :
  ∀ σ₀ e₀ τ φ,
    ok σ₀ →
    typing_reification σ₀ ⦰ e₀ τ φ →
    (∃ σ₁ e₁, (⟨σ₀, e₀⟩ ⇝ ⟨σ₁, e₁⟩)) ∨ value e₀ :=
  by
  intros _ _ _ _ Hok Hτ
  apply progress.strengthened _ ⦰ _ _ _ Hok Hτ (by simp)
