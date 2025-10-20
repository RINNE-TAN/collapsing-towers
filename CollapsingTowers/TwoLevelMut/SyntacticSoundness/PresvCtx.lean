import CollapsingTowers.TwoLevelMut.SyntacticTyping.Defs
import Mathlib.Tactic.CC

lemma preservation.under_ctx𝔹 :
  ∀ σ₀ Γ B e₀ τ φ ω,
    ctx𝔹 B →
    typing σ₀ Γ 𝟙 B⟦e₀⟧ τ φ ω →
    ∃ τ𝕖 φ₀ φ𝔹 ω₀ ω𝔹,
      φ = φ₀ ∪ φ𝔹 ∧
      ω = ω₀ ∪ ω𝔹 ∧
      typing σ₀ Γ 𝟙 e₀ τ𝕖 φ₀ ω₀ ∧
      ∀ σ₁ Δ e₁ φ₁ ω₁,
        σ₀.length ≤ σ₁.length →
        typing σ₁ (Δ ++ Γ) 𝟙 e₁ τ𝕖 φ₁ ω₁ →
        typing σ₁ (Δ ++ Γ) 𝟙 B⟦e₁⟧ τ (φ₁ ∪ φ𝔹) (ω₁ ∪ ω𝔹) :=
  by
  intros σ₀ Γ B e₀ τ φ ω HB Hτ
  cases HB
  case appl₁ =>
    cases Hτ
    case app₁ τ𝕒 φ₀ φ₁ φ₂ ω₀ ω₁ ω₂ Harg HX =>
      exists .arrow τ𝕒 τ φ₀ ω₀, φ₁, φ₀ ∪ φ₂, ω₁, ω₀ ∪ ω₂
      constructor; cases φ₀ <;> cases φ₁ <;> cases φ₂ <;> simp
      constructor; cc
      constructor; apply HX
      intros σ₁ Δ e₁ φ ω Hσ HX
      have HEqφ : φ ∪ (φ₀ ∪ φ₂) = φ₀ ∪ φ ∪ φ₂ := by cases φ₀ <;> cases φ₂ <;> simp
      have HEqω : ω ∪ (ω₀ ∪ ω₂) = ω₀ ∪ ω ∪ ω₂ := by cc
      rw [HEqφ, HEqω]
      apply typing.app₁
      . apply HX
      . apply typing.weakening.store _ _ _ _ _ _ _ _ Hσ
        apply typing.weakening _ _ _ _ _ _ _ _ Harg
  case appr₁ =>
    cases Hτ
    case app₁ τ𝕒 φ₀ φ₁ φ₂ ω₀ ω₁ ω₂ HX Hf =>
      exists τ𝕒, φ₂, φ₀ ∪ φ₁, ω₂, ω₀ ∪ ω₁
      constructor; cases φ₀ <;> cases φ₁ <;> cases φ₂ <;> simp
      constructor; cc
      constructor; apply HX
      intros σ₁ Δ e₁ φ ω Hσ HX
      have HEqφ : φ ∪ (φ₀ ∪ φ₁) = φ₀ ∪ φ₁ ∪ φ := by cases φ₀ <;> cases φ₁ <;> simp
      have HEqω : ω ∪ (ω₀ ∪ ω₁) = ω₀ ∪ ω₁ ∪ ω := by cc
      rw [HEqφ, HEqω]
      apply typing.app₁
      . apply typing.weakening.store _ _ _ _ _ _ _ _ Hσ
        apply typing.weakening _ _ _ _ _ _ _ _ Hf
      . apply HX
  case appl₂ =>
    cases Hτ
    case app₂ τ𝕒 τ𝕓 φ₁ φ₂ ω₀ ω₁ ω₂ HX Harg =>
      exists .fragment (.arrow τ𝕒 τ𝕓 ⊥ ω₀), φ₁, ⊤, ω₁, ω₀ ∪ ω₂
      constructor; simp
      constructor; cc
      constructor; apply HX
      intros σ₁ Δ e₁ φ ω Hσ HX; simp
      have HEqω : ω ∪ (ω₀ ∪ ω₂) = ω₀ ∪ ω ∪ ω₂ := by cc
      rw [HEqω]
      apply typing.app₂
      . apply HX
      . apply typing.weakening.store _ _ _ _ _ _ _ _ Hσ
        apply typing.weakening _ _ _ _ _ _ _ _ Harg
  case appr₂ =>
    cases Hτ
    case app₂ τ𝕒 τ𝕓 φ₁ φ₂ ω₀ ω₁ ω₂ Hf HX =>
      exists .fragment τ𝕒, φ₂, ⊤, ω₂, ω₀ ∪ ω₁
      constructor; simp
      constructor; cc
      constructor; apply HX
      intros σ₁ Δ e₁ φ ω Hσ HX; simp
      have HEqω : ω ∪ (ω₀ ∪ ω₁) = ω₀ ∪ ω₁ ∪ ω := by cc
      rw [HEqω]
      apply typing.app₂
      . apply typing.weakening.store _ _ _ _ _ _ _ _ Hσ
        apply typing.weakening _ _ _ _ _ _ _ _ Hf
      . apply HX
  case lift =>
    cases Hτ
    case lift_lam τ𝕒 τ𝕓 φ₀ φ₁ ω₀ Hω HX =>
      exists .arrow (.fragment τ𝕒) (.fragment τ𝕓) φ₀ ω₀, φ₁, ⊤, ω, ∅
      constructor; simp
      constructor; simp
      constructor; apply HX
      intros σ₁ Δ e₁ φ ω Hσ HX; simp
      apply typing.lift_lam; apply HX; apply Hω
    case lift_lit φ₀ HX =>
      exists .nat, φ₀, ⊤, ω, ∅
      constructor; simp
      constructor; simp
      constructor; apply HX
      intros σ₁ Δ e₁ φ ω Hσ HX; simp
      apply typing.lift_lit; apply HX
    case lift_unit φ₀ HX =>
      exists .unit, φ₀, ⊤, ω, ∅
      constructor; simp
      constructor; simp
      constructor; apply HX
      intros σ₁ Δ e₁ φ ω Hσ HX; simp
      apply typing.lift_unit; apply HX
  case lets e Hlc =>
    cases Hτ
    case lets τ𝕒 φ₀ φ₁ ω₀ ω₁ Hwbt HX Hclosed He =>
      exists τ𝕒, φ₀, φ₁, ω₀, ω₁
      constructor; simp
      constructor; cc
      constructor; apply HX
      intros σ₁ Δ e₁ φ ω Hσ HX
      apply typing.lets
      . apply HX
      . have HEq : ({0 ↦ (Δ ++ Γ).length}e) = (shiftl Γ.length Δ.length {0 ↦ Γ.length}e) :=
          by simp [comm.shiftl_opening, identity.shiftl _ _ _ Hclosed, Nat.add_comm]
        rw [HEq]
        apply typing.weakening.store _ _ _ _ _ _ _ _ Hσ
        apply typing.weakening.strengthened _ _ [(τ𝕒, 𝟙)] _ _ _ _ _ _ _ He (by simp)
      . apply Hwbt
      . apply closed.inc; apply Hclosed; simp
  case alloc₁ =>
    cases Hτ
    case alloc₁ ω HX =>
      exists .nat, φ, ⊥, ω, { .init 𝟙 }
      constructor; simp
      constructor; cc
      constructor; apply HX
      intros σ₁ Δ e₁ φ ω Hσ HX; simp [-Set.union_singleton]
      apply typing.alloc₁
      apply HX
  case alloc₂ =>
    cases Hτ
    case alloc₂ φ ω HX =>
      exists .fragment .nat, φ, ⊤, ω, { .init 𝟚 }
      constructor; simp
      constructor; cc
      constructor; apply HX
      intros σ₁ Δ e₁ φ ω Hσ HX; simp [-Set.union_singleton]
      apply typing.alloc₂
      apply HX
  case load₁ =>
    cases Hτ
    case load₁ ω HX =>
      exists .ref .nat, φ, ⊥, ω, { .read 𝟙 }
      constructor; simp
      constructor; cc
      constructor; apply HX
      intros σ₁ Δ e₁ φ ω Hσ HX; simp [-Set.union_singleton]
      apply typing.load₁
      apply HX
  case load₂ =>
    cases Hτ
    case load₂ φ ω HX =>
      exists .fragment (.ref .nat), φ, ⊤, ω, { .read 𝟚 }
      constructor; simp
      constructor; cc
      constructor; apply HX
      intros σ₁ Δ e₁ φ ω Hσ HX; simp [-Set.union_singleton]
      apply typing.load₂
      apply HX
  case storel₁ =>
    cases Hτ
    case store₁ φ₀ φ₁ ω₀ ω₁ HX Hr =>
      exists .ref .nat, φ₀, φ₁, ω₀, ω₁ ∪ { .write 𝟙 }
      constructor; simp
      constructor; cc
      constructor; apply HX
      intros σ₁ Δ e₁ φ ω Hσ HX
      have HEqω : ω ∪ (ω₁ ∪ {.write 𝟙}) = ω ∪ ω₁ ∪ {.write 𝟙} := by cc
      rw [HEqω]
      apply typing.store₁
      . apply HX
      . apply typing.weakening.store _ _ _ _ _ _ _ _ Hσ
        apply typing.weakening _ _ _ _ _ _ _ _ Hr
  case storer₁ =>
    cases Hτ
    case store₁ φ₀ φ₁ ω₀ ω₁ Hl HX =>
      exists .nat, φ₁, φ₀, ω₁, ω₀ ∪ { .write 𝟙 }
      constructor; cases φ₀ <;> cases φ₁ <;> simp
      constructor; cc
      constructor; apply HX
      intros σ₁ Δ e₁ φ ω Hσ HX
      have HEqφ : φ ∪ φ₀ = φ₀ ∪ φ := by cases φ₀ <;> simp
      have HEqω : ω ∪ (ω₀ ∪ {.write 𝟙}) = ω₀ ∪ ω ∪ {.write 𝟙} := by cc
      rw [HEqφ, HEqω]
      apply typing.store₁
      . apply typing.weakening.store _ _ _ _ _ _ _ _ Hσ
        apply typing.weakening _ _ _ _ _ _ _ _ Hl
      . apply HX
  case storel₂ =>
    cases Hτ
    case store₂ φ₀ φ₁ ω₀ ω₁ HX Hr =>
      exists .fragment (.ref .nat), φ₀, ⊤, ω₀, ω₁ ∪ { .write 𝟚 }
      constructor; simp
      constructor; cc
      constructor; apply HX
      intros σ₁ Δ e₁ φ ω Hσ HX; simp [-Set.union_singleton]
      have HEqω : ω ∪ (ω₁ ∪ {.write 𝟚}) = ω ∪ ω₁ ∪ {.write 𝟚} := by cc
      rw [HEqω]
      apply typing.store₂
      . apply HX
      . apply typing.weakening.store _ _ _ _ _ _ _ _ Hσ
        apply typing.weakening _ _ _ _ _ _ _ _ Hr
  case storer₂ =>
    cases Hτ
    case store₂ φ₀ φ₁ ω₀ ω₁ Hl HX =>
      exists .fragment .nat, φ₁, ⊤, ω₁, ω₀ ∪ { .write 𝟚 }
      constructor; simp
      constructor; cc
      constructor; apply HX
      intros σ₁ Δ e₁ φ ω Hσ HX; simp [-Set.union_singleton]
      have HEqω : ω ∪ (ω₀ ∪ {.write 𝟚}) = ω₀ ∪ ω ∪ {.write 𝟚} := by cc
      rw [HEqω]
      apply typing.store₂
      . apply typing.weakening.store _ _ _ _ _ _ _ _ Hσ
        apply typing.weakening _ _ _ _ _ _ _ _ Hl
      . apply HX

lemma preservation.under_ctxℝ :
  ∀ σ₀ intro Γ R e₀ τ φ ω,
    ctxℝ intro Γ.length R →
    lc e₀ →
    typing σ₀ Γ 𝟙 R⟦e₀⟧ τ φ ω →
    ∃ Δ τ𝕖 φ₀ ω₀,
    ∃ ωℝ : MEffects → MEffects,
      Δ.length = Γ.length + intro ∧
      ω = ωℝ ω₀ ∧
      (∀ ω₀ ω₁, ω₁ ≤ ω₀ → ωℝ ω₁ ≤ ωℝ ω₀) ∧
      typing_reification σ₀ Δ e₀ τ𝕖 φ₀ ω₀ ∧
      ∀ σ₁ e₁ φ₁ ω₁,
        σ₀.length ≤ σ₁.length →
        fv e₁ ⊆ fv e₀ →
        typing_reification σ₁ Δ e₁ τ𝕖 φ₁ ω₁ →
        typing σ₁ Γ 𝟙 R⟦e₁⟧ τ φ (ωℝ ω₁) :=
  by
  intros σ₀ intro Γ R e₀ τ φ ω HR Hlc Hτ
  cases HR
  case lam𝕔 =>
    cases Hτ
    case lam𝕔 τ𝕒 τ𝕓 φ₀ ω₀ Hwbt Hω HX Hclosed =>
      rw [identity.opening_closing _ _ _ Hlc] at HX
      exists (τ𝕒, 𝟚) :: Γ, .rep τ𝕓, φ₀, ω₀, fun _ => ∅
      constructor; simp
      constructor; simp
      constructor; simp
      constructor; apply HX
      intros σ₁ e₁ φ₁ ω₁ Hσ Hfv HX
      admit
  all_goals admit
