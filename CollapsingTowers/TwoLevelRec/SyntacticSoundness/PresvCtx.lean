import CollapsingTowers.TwoLevelRec.OperationalSemantics.Defs
import CollapsingTowers.TwoLevelRec.SyntacticTyping.Defs

lemma preservation.under_ctx𝔹 :
  ∀ Γ B e₀ e₁ τ φ,
    ctx𝔹 B →
    (∀ τ φ,
      typing Γ 𝟙 e₀ τ φ →
      typing Γ 𝟙 e₁ τ φ
    ) →
    typing Γ 𝟙 B⟦e₀⟧ τ φ →
    typing Γ 𝟙 B⟦e₁⟧ τ φ :=
  by
  intros Γ B e₀ e₁ τ φ HB IH Hτ
  cases HB
  case appl₁ =>
    cases Hτ
    case app₁ Harg HX =>
      have HX := IH _ _ HX
      apply typing.app₁; apply HX; apply Harg
  case appr₁ =>
    cases Hτ
    case app₁ φ₀ φ₁ φ₂ HX Hf =>
      have HX := IH _ _ HX
      apply typing.app₁; apply Hf; apply HX
  case appl₂ =>
    cases Hτ
    case app₂ HX Harg =>
      have HX := IH _ _ HX
      apply typing.app₂; apply HX; apply Harg
  case appr₂ =>
    cases Hτ
    case app₂ Hf HX =>
      have HX := IH _ _ HX
      apply typing.app₂; apply Hf; apply HX
  case binaryl₁ =>
    cases Hτ
    case binary₁ φ₀ φ₁ HX Hr =>
      have HX := IH _ _ HX
      apply typing.binary₁; apply HX; apply Hr
  case binaryr₁ =>
    cases Hτ
    case binary₁ φ₀ φ₁ Hl HX =>
      have HX := IH _ _ HX
      apply typing.binary₁; apply Hl; apply HX
  case binaryl₂ =>
    cases Hτ
    case binary₂ HX Hr =>
      have HX := IH _ _ HX
      apply typing.binary₂; apply HX; apply Hr
  case binaryr₂ =>
    cases Hτ
    case binary₂ Hl HX =>
      have HX := IH _ _ HX
      apply typing.binary₂; apply Hl; apply HX
  case lift =>
    cases Hτ
    case lift_lam HX =>
      have HX := IH _ _ HX
      apply typing.lift_lam; apply HX
    case lift_lit HX =>
      have HX := IH _ _ HX
      apply typing.lift_lit; apply HX
  case lets =>
    cases Hτ
    case lets φ₀ φ₁ Hwbt HX Hclosed He =>
      have HX := IH _ _ HX
      apply typing.lets; apply HX; apply He; apply Hwbt; apply Hclosed
  case fix₁ =>
    cases Hτ
    case fix₁ Hfixφ HX =>
      have HX := IH _ _ HX
      apply typing.fix₁; apply Hfixφ; apply HX
  case fix₂ =>
    cases Hτ
    case fix₂ HX =>
      have HX := IH _ _ HX
      apply typing.fix₂; apply HX
  case ifz₁ =>
    cases Hτ
    case ifz₁ φ₀ φ₁ φ₂ HX Hl Hr =>
      have HX := IH _ _ HX
      apply typing.ifz₁; apply HX; apply Hl; apply Hr
  case ifz₂ =>
    cases Hτ
    case ifz₂ HX Hl Hr =>
      have HX := IH _ _ HX
      apply typing.ifz₂; apply HX; apply Hl; apply Hr

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
  case ifzl₂ =>
    cases Hτ
    case ifz₂ Hc HX Hr =>
      cases HX
      case pure HX =>
        have HX := IH _ _ _ (by simp) HX
        apply typing.ifz₂; apply Hc; apply typing_reification.pure _ _ _ HX; apply Hr
      case reify HX =>
        have HX := IH _ _ _ (by simp) HX
        apply typing.ifz₂; apply Hc; apply typing_reification.reify _ _ _ _ HX; apply Hr
  case ifzr₂ =>
    cases Hτ
    case ifz₂ Hc Hl HX =>
      cases HX
      case pure HX =>
        have HX := IH _ _ _ (by simp) HX
        apply typing.ifz₂; apply Hc; apply Hl; apply typing_reification.pure _ _ _ HX
      case reify HX =>
        have HX := IH _ _ _ (by simp) HX
        apply typing.ifz₂; apply Hc; apply Hl; apply typing_reification.reify _ _ _ _ HX

lemma preservation.under_ctx𝔼 :
  ∀ Γ E e τ φ,
    ctx𝔼 E →
    typing Γ 𝟙 E⟦e⟧ τ φ →
    ∃ τ𝕖 φ𝕖 φ𝔼,
      φ = φ𝕖 ∪ φ𝔼 ∧
      typing Γ 𝟙 e τ𝕖 φ𝕖 ∧
      ∀ Δ e φ,
        typing (Δ ++ Γ) 𝟙 e τ𝕖 φ →
        typing (Δ ++ Γ) 𝟙 E⟦e⟧ τ (φ ∪ φ𝔼) :=
  by
  intros Γ E e τ φ HE Hτ
  admit
