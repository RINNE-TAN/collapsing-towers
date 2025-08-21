import CollapsingTowers.TwoLevelRec.SyntacticSoundness.PresvCtx

lemma preservation.reflect :
  ∀ Γ E e τ φ₀,
    ctx𝔼 E →
    typing_reification Γ E⟦.reflect e⟧ τ φ₀ →
    ∃ φ₁,
      typing_reification Γ (.lets𝕔 e E⟦.code (.bvar 0)⟧) τ φ₁ ∧
      φ₁ ≤ φ₀ :=
  by
  intros Γ E e τ φ₀ HE Hτ
  admit

lemma preservation.reify :
  ∀ Γ intro R e₀ e₁ τ φ₀,
    ctxℝ intro Γ.length R →
    lc e₀ →
    fv e₁ ⊆ fv e₀ →
    (∀ Γ τ φ₀,
      typing_reification Γ e₀ τ φ₀ →
      ∃ φ₁,
        typing_reification Γ e₁ τ φ₁ ∧
        φ₁ ≤ φ₀
    ) →
    typing Γ 𝟚 R⟦e₀⟧ τ φ₀ →
    ∃ φ₁,
      typing Γ 𝟚 R⟦e₁⟧ τ φ₁ ∧
      φ₁ ≤ φ₀ :=
  by
  intros Γ intro R e₀ e₁ τ φ₀ HR Hlc Hfv IH Hτ
  cases HR
  case lam𝕔 =>
    cases Hτ
    case lam𝕔 τ𝕒 τ𝕓 _ Hwbt HX Hclosed =>
      rw [identity.opening_closing _ _ _ Hlc] at HX
      have ⟨φₓ, HX, Hφ⟩ := IH _ _ _ HX
      exists ⊤
      constructor
      . apply typing.lam𝕔
        . rw [identity.opening_closing]
          apply HX
          apply typing_reification.regular _ _ _ _ HX
        . apply Hwbt
        . rw [← closed.under_closing]
          apply typing_reification.closed_at_env _ _ _ _ HX
      . simp
  case lets𝕔 =>
    cases Hτ
    case lets𝕔 τ𝕒 τ𝕓 _ Hwbt Hb HX Hclosed =>
      rw [identity.opening_closing _ _ _ Hlc] at HX
      have ⟨φₓ, HX, Hφ⟩ := IH _ _ _ HX
      exists ⊥
      constructor
      . apply typing.lets𝕔
        . apply Hb
        . rw [identity.opening_closing]
          apply HX
          apply typing_reification.regular _ _ _ _ HX
        . apply Hwbt
        . rw [← closed.under_closing]
          apply typing_reification.closed_at_env _ _ _ _ HX
      . simp
  case run =>
    cases Hτ
    case run Hclosed HX =>
      have ⟨φₓ, HX, Hφ⟩ := IH _ _ _ HX
      exists ⊥
      constructor
      . apply typing.run
        . apply HX
        . rw [closed_iff_fv_empty] at Hclosed
          simp [Hclosed] at Hfv
          rw [closed_iff_fv_empty, Hfv]
      . simp
  case ifzl₂ =>
    cases Hτ
    case ifz₂ Hc HX Hr =>
      have ⟨φₓ, HX, Hφ⟩ := IH _ _ _ HX
      exists ⊤
      constructor
      . apply typing.ifz₂
        . apply Hc
        . apply HX
        . apply Hr
      . simp
  case ifzr₂ =>
    cases Hτ
    case ifz₂ Hc Hl HX =>
      have ⟨φₓ, HX, Hφ⟩ := IH _ _ _ HX
      exists ⊤
      constructor
      . apply typing.ifz₂
        . apply Hc
        . apply Hl
        . apply HX
      . simp
