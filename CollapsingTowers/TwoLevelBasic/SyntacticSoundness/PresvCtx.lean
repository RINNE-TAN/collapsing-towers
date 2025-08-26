import CollapsingTowers.TwoLevelBasic.SyntacticTyping.Defs

lemma preservation.under_ctx𝔹 :
  ∀ Γ B e τ φ,
    ctx𝔹 B →
    typing Γ 𝟙 B⟦e⟧ τ φ →
    ∃ τ𝕖 φ𝕖 φ𝔹,
      φ = φ𝕖 ∪ φ𝔹 ∧
      typing Γ 𝟙 e τ𝕖 φ𝕖 ∧
      ∀ Δ e φ,
        typing (Δ ++ Γ) 𝟙 e τ𝕖 φ →
        typing (Δ ++ Γ) 𝟙 B⟦e⟧ τ (φ ∪ φ𝔹) :=
  by
  intros Γ B e τ φ HB Hτ
  cases HB
  case appl₁ =>
    cases Hτ
    case app₁ τ𝕒 φ₀ φ₁ φ₂ Harg HX =>
      exists τ𝕒.arrow τ φ₀, φ₁, (φ₀ ∪ φ₂)
      constructor; cases φ₀ <;> cases φ₁ <;> cases φ₂ <;> simp
      constructor; apply HX
      intros Δ eₓ φ HX
      have HEqφ : φ ∪ (φ₀ ∪ φ₂) = φ₀ ∪ φ ∪ φ₂ := by cases φ₀ <;> cases φ₂ <;> simp
      rw [HEqφ]
      apply typing.app₁; apply HX; apply typing.weakening _ _ _ _ _ _ Harg
  case appr₁ =>
    cases Hτ
    case app₁ τ𝕒 φ₀ φ₁ φ₂ HX Hf =>
      exists τ𝕒, φ₂, (φ₀ ∪ φ₁)
      constructor; cases φ₀ <;> cases φ₁ <;> cases φ₂ <;> simp
      constructor; apply HX
      intros Δ eₓ φ HX
      have HEqφ : φ ∪ (φ₀ ∪ φ₁) = φ₀ ∪ φ₁ ∪ φ := by cases φ₀ <;> cases φ₁ <;> simp
      rw [HEqφ]
      apply typing.app₁; apply typing.weakening _ _ _ _ _ _ Hf; apply HX
  case appl₂ =>
    cases Hτ
    case app₂ τ𝕒 τ𝕓 φ₀ φ₁ HX Harg =>
      exists .fragment (.arrow τ𝕒 τ𝕓 ⊥), φ₀, ⊤
      constructor; simp
      constructor; apply HX
      intros Δ eₓ φ HX; simp
      apply typing.app₂; apply HX; apply typing.weakening _ _ _ _ _ _ Harg
  case appr₂ =>
    cases Hτ
    case app₂ τ𝕒 τ𝕓 φ₀ φ₁ Hf HX =>
      exists .fragment τ𝕒, φ₁, ⊤
      constructor; simp
      constructor; apply HX
      intros Δ eₓ φ HX; simp
      apply typing.app₂; apply typing.weakening _ _ _ _ _ _ Hf; apply HX
  case lift =>
    cases Hτ
    case lift_lam τ𝕒 τ𝕓 φ₀ φ₁ HX =>
      exists .arrow (.fragment τ𝕒) (.fragment τ𝕓) φ₀, φ₁, ⊤
      constructor; simp
      constructor; apply HX
      intros Δ eₓ φ HX; simp
      apply typing.lift_lam; apply HX
    case lift_lit φ₀ HX =>
      exists .nat, φ₀, ⊤
      constructor; simp
      constructor; apply HX
      intros Δ eₓ φ HX; simp
      apply typing.lift_lit; apply HX
  case lets e Hlc =>
    cases Hτ
    case lets τ𝕒 φ₀ φ₁ Hwbt HX Hclosed He =>
      exists τ𝕒, φ₀, φ₁
      constructor; simp
      constructor; apply HX
      intros Δ eₓ φ HX
      apply typing.lets
      . apply HX
      . have HEq : ({0 ↦ (Δ ++ Γ).length}e) = (shiftl Γ.length Δ.length {0 ↦ Γ.length}e) :=
          by simp [comm.shiftl_opening, identity.shiftl _ _ _ Hclosed, Nat.add_comm]
        rw [HEq]
        apply typing.weakening.strengthened _ [(τ𝕒, 𝟙)] _ _ _ _ _ _ He (by simp)
      . apply Hwbt
      . apply closed.inc; apply Hclosed; simp

lemma preservation.under_ctxℝ :
  ∀ intro Γ R e₀ e₁ τ φ,
    ctxℝ intro Γ.length R →
    lc e₀ →
    fv e₁ ⊆ fv e₀ →
    (∀ Δ τ φ,
      Δ.length = Γ.length + intro →
      typing Δ 𝟙 e₀ τ φ →
      typing Δ 𝟙 e₁ τ φ
    ) →
    typing Γ 𝟙 R⟦e₀⟧ τ φ →
    typing Γ 𝟙 R⟦e₁⟧ τ φ :=
  by
  intros intro Γ R e₀ e₁ τ φ HR Hlc Hfv IH Hτ
  cases HR
  case lam𝕔 =>
    cases Hτ
    case lam𝕔 Hwbt HX Hclosed =>
      rw [identity.opening_closing _ _ _ Hlc] at HX
      cases HX
      case pure HX =>
        have HX := IH (_ :: Γ) _ _ (by simp) HX
        apply typing.lam𝕔
        . apply typing_reification.pure
          rw [identity.opening_closing _ _ _ (typing.regular _ _ _ _ _ HX)]
          apply HX
        . apply Hwbt
        . rw [← closed.under_closing]
          apply typing.closed_at_env _ _ _ _ _ HX
      case reify HX =>
        have HX := IH (_ :: Γ) _ _ (by simp) HX
        apply typing.lam𝕔
        . apply typing_reification.reify
          rw [identity.opening_closing _ _ _ (typing.regular _ _ _ _ _ HX)]
          apply HX
        . apply Hwbt
        . rw [← closed.under_closing]
          apply typing.closed_at_env _ _ _ _ _ HX
  case lets𝕔 =>
    cases Hτ
    case lets𝕔 Hwbt Hb HX Hclosed =>
      rw [identity.opening_closing _ _ _ Hlc] at HX
      cases HX
      case pure HX =>
        have HX := IH (_ :: Γ) _ _ (by simp) HX
        apply typing.lets𝕔
        . apply Hb
        . apply typing_reification.pure
          rw [identity.opening_closing _ _ _ (typing.regular _ _ _ _ _ HX)]
          apply HX
        . apply Hwbt
        . rw [← closed.under_closing]
          apply typing.closed_at_env _ _ _ _ _ HX
      case reify HX =>
        have HX := IH (_ :: Γ) _ _ (by simp) HX
        apply typing.lets𝕔
        . apply Hb
        . apply typing_reification.reify
          rw [identity.opening_closing _ _ _ (typing.regular _ _ _ _ _ HX)]
          apply HX
        . apply Hwbt
        . rw [← closed.under_closing]
          apply typing.closed_at_env _ _ _ _ _ HX
  case run =>
    cases Hτ
    case run Hclosed HX =>
      cases HX
      case pure HX =>
        have HX := IH _ _ _ (by simp) HX
        apply typing.run
        . apply typing_reification.pure _ _ _ HX
        . rw [closed_iff_fv_empty] at Hclosed
          simp [Hclosed] at Hfv
          rw [closed_iff_fv_empty, Hfv]
      case reify HX =>
        have HX := IH _ _ _ (by simp) HX
        apply typing.run
        . apply typing_reification.reify _ _ _ _ HX
        . rw [closed_iff_fv_empty] at Hclosed
          simp [Hclosed] at Hfv
          rw [closed_iff_fv_empty, Hfv]

lemma preservation.under_ctx𝔼 :
  ∀ Γ E e τ φ,
    ctx𝔼 E →
    typing Γ 𝟙 E⟦e⟧ τ φ →
    ∃ τ𝕖 φ𝕖 φ𝔹,
      φ = φ𝕖 ∪ φ𝔹 ∧
      typing Γ 𝟙 e τ𝕖 φ𝕖 ∧
      ∀ Δ e φ,
        typing (Δ ++ Γ) 𝟙 e τ𝕖 φ →
        typing (Δ ++ Γ) 𝟙 E⟦e⟧ τ (φ ∪ φ𝔹) :=
  by
  intros Γ E e τ φ HE Hτ
  induction HE generalizing τ φ
  case hole =>
    exists τ, φ, ⊥
    constructor; cases φ <;> rfl
    constructor; apply Hτ
    intros Δ e φ Hτ; simp; apply Hτ
  case cons𝔹 B E HB HE IH =>
    have ⟨τ𝕖, φ₀, φ₁, HEqφ₀, Hτ, IHτB⟩ := preservation.under_ctx𝔹 _ _ _ _ _ HB Hτ
    have ⟨τ𝕖, φ₂, φ₃, HEqφ₁, Hτ, IHτE⟩ := IH _ _ Hτ
    rw [HEqφ₀, HEqφ₁]
    exists τ𝕖, φ₂, φ₁ ∪ φ₃
    constructor; cases φ₀ <;> cases φ₁ <;> cases φ₂ <;> cases φ₃ <;> simp
    constructor; apply Hτ
    intros Δ e φ Hτ
    have Hτ := IHτE _ _ _ Hτ
    have Hτ := IHτB _ _ _ Hτ
    have HEqφ : φ ∪ (φ₁ ∪ φ₃) = φ ∪ φ₃ ∪ φ₁ := by cases φ₁ <;> cases φ₃ <;> simp
    rw [HEqφ]; apply Hτ
