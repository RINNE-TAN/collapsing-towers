
import CollapsingTowers.TwoLevelPCP.Preservation.Head
import CollapsingTowers.TwoLevelPCP.Preservation.Store
import CollapsingTowers.TwoLevelPCP.Preservation.Reflect
theorem preservation_strengthened :
  ∀ Γ σ₀ st₀ st₁ e₀ e₁ τ φ₀,
    step_lvl Γ.length (st₀, e₀) (st₁, e₁) →
    well_store σ₀ st₀ →
    typing_reification Γ σ₀ e₀ τ φ₀ →
    ∃ σ₁ φ₁,
      well_store (σ₁ ++ σ₀) st₁ ∧
      typing_reification Γ (σ₁ ++ σ₀) e₁ τ φ₁ ∧
      φ₁ ≤ φ₀ :=
  by
  intro Γ σ₀ st₀ st₁ e₀ e₁ τ φ₀ Hstep HwellStore Hτ
  cases Hstep
  case step𝕄 M e₀ e₁ HM Hlc Hhead𝕄 =>
    have HFv : fv e₁ ⊆ fv e₀ := by apply fv_head𝕄; apply Hhead𝕄
    have IH :
      ∀ Γ τ φ₀,
        typing Γ σ₀ .stat e₀ τ φ₀ →
        ∃ φ₁,
          typing Γ σ₀ .stat e₁ τ φ₁ ∧
          φ₁ ≤ φ₀ :=
      by
      intros _ _ _; apply preservation_head𝕄
      apply Hhead𝕄; apply Hlc
    exists []
    cases Hτ
    case pure Hτ =>
      have ⟨φ₁, Hτ, Hφ⟩ := decompose𝕄_head _ _ _ _ _ _ _ HM Hlc HFv IH Hτ
      rw [le_pure _ Hφ] at Hτ
      exists ∅
      constructor; apply HwellStore
      constructor; apply typing_reification.pure; apply Hτ
      rfl
    case reify Hτ =>
      have ⟨φ₁, Hτ, Hφ⟩ := decompose𝕄_head _ _ _ _ _ _ _ HM Hlc HFv IH Hτ
      exists φ₁
      constructor; apply HwellStore
      constructor; apply typing_reification.reify; apply Hτ
      apply Hφ
  case store𝕄 HM Hlc Hstore𝕄 =>
    cases Hτ
    case pure Hτ =>
      have ⟨σ₁, HwellStore, Hτ⟩ := preservation_store𝕄 _ _ _ _ _ _ _ _ _ HM Hlc Hstore𝕄 Hτ HwellStore
      exists σ₁, ∅
      constructor; apply HwellStore
      constructor; apply typing_reification.pure; apply Hτ; rfl
    case reify Hτ =>
      have ⟨σ₁, HwellStore, Hτ⟩ := preservation_store𝕄 _ _ _ _ _ _ _ _ _ HM Hlc Hstore𝕄 Hτ HwellStore
      exists σ₁, φ₀
      constructor; apply HwellStore
      constructor; apply typing_reification.reify; apply Hτ; rfl
  case reflect P E e HP HE Hlc =>
    cases HP
    case hole =>
      exists [], ∅; constructor
      . apply HwellStore
      . simp; apply preservation_reflect
        apply HE; apply Hτ
    case consℚ HQ =>
      exists [], φ₀; constructor
      . apply HwellStore
      . cases Hτ
        all_goals
          next Hτ =>
          simp; constructor
          apply decomposeℚ_reflect
          apply HQ; apply HE; apply Hlc; apply Hτ

theorem preservation :
  ∀ σ₀ st₀ st₁ e₀ e₁ τ φ₀,
    step (st₀, e₀) (st₁, e₁) →
    well_store σ₀ st₀ →
    typing_reification [] σ₀ e₀ τ φ₀ →
    ∃ σ₁ φ₁,
      well_store (σ₁ ++ σ₀) st₁ ∧
      typing_reification [] (σ₁ ++ σ₀) e₁ τ φ₁ ∧
      φ₁ ≤ φ₀ :=
  by
  intros σ₀ st₀ st₁ e₀ e₁ τ φ₀ Hstep
  apply preservation_strengthened
  apply Hstep

theorem preservation_stepn :
  ∀ σ₀ st₀ st₁ e₀ e₁ τ φ₀,
    stepn (st₀, e₀) (st₁, e₁) →
    well_store σ₀ st₀ →
    typing_reification [] σ₀ e₀ τ φ₀ →
    ∃ σ₁ φ₁,
      well_store (σ₁ ++ σ₀) st₁ ∧
      typing_reification [] (σ₁ ++ σ₀) e₁ τ φ₁ ∧
      φ₁ ≤ φ₀ :=
  by
  intro σ₀ st₀ st₁ e₀ e₁ τ φ₀ Hstepn HwellStore Hτ
  generalize HEq : (st₁, e₁) = E₁
  rw [HEq] at Hstepn
  induction Hstepn generalizing st₁ e₁ with
  | refl =>
    simp at HEq; rw [HEq.left, HEq.right]
    exists [], φ₀
  | multi E₁' E₂' _ Hstep IHτ =>
    have ⟨st₁', e₁'⟩ := E₁'
    have ⟨st₂', e₂'⟩ := E₂'
    simp at HEq; rw [HEq.left, HEq.right]
    have ⟨σ₁, φ₁, HwellStore₁, IHτ₁, HφLe₁⟩ := IHτ st₁' e₁' rfl
    have ⟨σ₂, φ₂, HwellStore₂, IHτ₂, HφLe₂⟩ := preservation _ _ _ _ _ _ _ Hstep HwellStore₁ IHτ₁
    exists (σ₂ ++ σ₁), φ₂
    rw [List.append_assoc]
    constructor; apply HwellStore₂
    constructor; apply IHτ₂
    apply le_trans; apply HφLe₂; apply HφLe₁
