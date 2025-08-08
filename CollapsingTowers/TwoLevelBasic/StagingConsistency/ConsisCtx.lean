import CollapsingTowers.TwoLevelBasic.LogicEquiv.Defs

-- Γ ⊢ e₀ : τ →
-- ‖Γ‖ ⊨ ‖e₀‖ ≈ ‖e₁‖ : ‖τ‖
-- ————————————————————————————
-- Γ ⊢ B⟦e₀⟧ : τ →
-- ‖Γ‖ ⊨ ‖B⟦e₀⟧‖ ≈ ‖B⟦e₁⟧‖ : ‖τ‖
lemma consistency.under_ctx𝔹 :
  ∀ Γ B e₀ e₁ τ φ,
    ctx𝔹 B →
    (∀ τ φ,
      typing Γ 𝟙 e₀ τ φ →
      logic_equiv_typing ‖Γ‖𝛾 ‖e₀‖ ‖e₁‖ ‖τ‖𝜏
    ) →
    typing Γ 𝟙 B⟦e₀⟧ τ φ →
    logic_equiv_typing ‖Γ‖𝛾 ‖B⟦e₀⟧‖ ‖B⟦e₁⟧‖ ‖τ‖𝜏 :=
  by
  intros Γ B e₀ e₁ τ φ HB IH Hτ
  cases HB
  case appl₁ =>
    cases Hτ
    case app₁ τ𝕒 _ _ _ Harg HX =>
      apply compatibility.app
      apply IH (.arrow τ𝕒 τ _); apply HX
      apply typing.erase.fundamental; apply Harg
  case appr₁ =>
    cases Hτ
    case app₁ τ𝕒 _ _ _ HX Hf =>
      apply compatibility.app
      apply typing.erase.fundamental _ _ _ (.arrow τ𝕒 τ _); apply Hf
      apply IH; apply HX
  case appl₂ =>
    cases Hτ
    case app₂ τ𝕒 τ𝕓 _ _ HX Harg =>
      apply compatibility.app
      apply IH (.fragment (.arrow τ𝕒 τ𝕓 _)); apply HX
      apply typing.erase.fundamental _ _ _ (.fragment τ𝕒); apply Harg
  case appr₂ =>
    cases Hτ
    case app₂ τ𝕒 τ𝕓 _ _ Hf HX =>
      apply compatibility.app
      apply typing.erase.fundamental _ _ _ (.fragment (.arrow τ𝕒 τ𝕓 _)); apply Hf
      apply IH (.fragment τ𝕒); apply HX
  case lift =>
    cases Hτ
    case lift_lam τ𝕒 τ𝕓 _ _ HX =>
      apply IH (.arrow (.fragment τ𝕒) (.fragment τ𝕓) _); apply HX
    case lift_lit HX =>
      apply IH .nat; apply HX
  case lets Hlc =>
    cases Hτ
    case lets HX Hclose He =>
      have Hsem := IH _ _ HX
      have ⟨Hwf₀, Hwf₁, _⟩ := Hsem
      apply compatibility.lets
      constructor
      . apply Hwf₀.right
      . rw [← env.erase.length, ← closed.under_erase]; apply Hclose
      constructor
      . apply Hwf₁.right
      . rw [← env.erase.length, ← closed.under_erase]; apply Hclose
      apply Hsem
      rw [← env.erase, ← comm.erase_opening]; apply typing.erase.fundamental
      rw [← env.erase.length]; apply He

-- Γ ⊢ e₀ : τ →
-- ‖Γ‖ ⊨ ‖e₀‖ ≈ ‖e₁‖ : ‖τ‖
-- ————————————————————————————
-- Γ ⊢ R⟦e₀⟧ : τ →
-- ‖Γ‖ ⊨ ‖R⟦e₀⟧‖ ≈ ‖R⟦e₁⟧‖ : ‖τ‖
lemma consistency.under_ctxℝ :
  ∀ intro Γ R e₀ e₁ τ φ,
    ctxℝ intro Γ.length R →
    lc e₀ →
    (∀ Δ τ φ,
      Δ.length = intro →
      typing (Δ ++ Γ) 𝟙 e₀ τ φ →
      logic_equiv_typing ‖Δ ++ Γ‖𝛾 ‖e₀‖ ‖e₁‖ ‖τ‖𝜏
    ) →
    typing Γ 𝟙 R⟦e₀⟧ τ φ →
    logic_equiv_typing ‖Γ‖𝛾 ‖R⟦e₀⟧‖ ‖R⟦e₁⟧‖ ‖τ‖𝜏 :=
  by
  intros intro Γ R e₀ e₁ τ φ HR Hlc IH Hτ
  cases HR
  case lam𝕔 =>
    cases Hτ
    case lam𝕔 _ _ _ _ Hτ Hclose =>
      cases Hτ
      all_goals
      next Hτ =>
        rw [← List.singleton_append, identity.opening_closing _ _ _ Hlc] at Hτ
        have Hsem := IH _ _ _ (by simp) Hτ
        have ⟨Hwf₀, Hwf₁, _⟩ := Hsem
        apply compatibility.lam
        . simp [← env.erase.length, ← closed.under_erase]; apply Hclose
        . simp [← env.erase.length, ← closed.under_erase, ← closed.under_closing]
          rw [← env.erase.length] at Hwf₁
          rw [closed.under_erase]; apply Hwf₁.right
        rw [← comm.erase_opening, ← comm.erase_opening]
        rw [← env.erase.length, identity.opening_closing, identity.opening_closing]
        apply Hsem
        . rw [lc.under_erase]; apply Hwf₁.left
        . apply Hlc
  case lets𝕔 =>
    cases Hτ
    case lets𝕔 Hτb Hτe Hclose =>
      cases Hτe
      all_goals
      next Hτe =>
        rw [← List.singleton_append, identity.opening_closing _ _ _ Hlc] at Hτe
        have Hsem := IH _ _ _ (by simp) Hτe
        have ⟨Hwf₀, Hwf₁, _⟩ := Hsem
        apply compatibility.lets
        constructor
        . simp [← env.erase.length, ← closed.under_erase]; apply typing.closed_at_env; apply Hτb
        . simp [← env.erase.length, ← closed.under_erase]; apply Hclose
        constructor
        . simp [← env.erase.length, ← closed.under_erase]; apply typing.closed_at_env; apply Hτb
        . simp [← env.erase.length, ← closed.under_erase, ← closed.under_closing]
          rw [← env.erase.length] at Hwf₁
          rw [closed.under_erase]; apply Hwf₁.right
        apply typing.erase.fundamental; apply Hτb
        rw [← comm.erase_opening, ← comm.erase_opening]
        rw [← env.erase.length, identity.opening_closing, identity.opening_closing]
        apply Hsem
        . rw [lc.under_erase]; apply Hwf₁.left
        . apply Hlc
  case run =>
    cases Hτ
    case run Hτ =>
      cases Hτ
      case pure Hτ =>
        apply IH [] (.rep τ)
        simp; apply Hτ
      case reify Hτ =>
        apply IH [] (.fragment τ)
        simp; apply Hτ

-- Γ ⊢ E⟦e⟧ : τ
-- ————————————————————————————————————
-- ∃ τ𝕖,
--   ‖Γ‖ ⊨ ‖e‖ ≈ ‖e‖ : ‖τ‖ ∧
--   ‖x ↦ τ𝕖, Γ‖ ⊨ ‖E⟦x⟧‖ ≈ ‖E⟦x⟧‖ : ‖τ‖
lemma consistency.under_ctx𝔼 :
  ∀ Γ E e τ φ,
    ctx𝔼 E →
    typing Γ 𝟙 E⟦e⟧ τ φ →
    ∃ τ𝕖,
      logic_equiv_typing ‖Γ‖𝛾 ‖e‖ ‖e‖ ‖τ𝕖‖𝜏 ∧
      logic_equiv_typing ‖(τ𝕖, 𝟙) :: Γ‖𝛾 ‖E⟦.fvar Γ.length⟧‖ ‖E⟦.fvar Γ.length⟧‖ ‖τ‖𝜏 :=
  by
  intros Γ E e τ φ HE Hτ
  induction HE generalizing τ φ
  case hole =>
    exists τ
    constructor; apply typing.erase.fundamental; apply Hτ
    apply compatibility.fvar
    apply env.erase.binds; simp; rfl
  case cons𝔹 B E HB HE IH =>
    cases HB
    case appl₁ =>
      cases Hτ
      case app₁ Harg HX =>
        have ⟨τ𝕖, Hsem𝕖, HsemX⟩ := IH _ _ HX
        exists τ𝕖
        constructor; apply Hsem𝕖
        apply compatibility.app
        apply HsemX
        apply typing.erase.fundamental _ _ _ _ _ (typing.weakening.singleton _ _ _ _ _ _ _ Harg)
    case appr₁ =>
      cases Hτ
      case app₁ HX Hf =>
        have ⟨τ𝕖, Hsem𝕖, HsemX⟩ := IH _ _ HX
        exists τ𝕖
        constructor; apply Hsem𝕖
        apply compatibility.app
        apply typing.erase.fundamental _ _ _ _ _ (typing.weakening.singleton _ _ _ _ _ _ _ Hf)
        apply HsemX
    case appl₂ =>
      cases Hτ
      case app₂ HX Harg =>
        have ⟨τ𝕖, Hsem𝕖, HsemX⟩ := IH _ _ HX
        exists τ𝕖
        constructor; apply Hsem𝕖
        apply compatibility.app
        apply HsemX
        apply typing.erase.fundamental _ _ _ _ _ (typing.weakening.singleton _ _ _ _ _ _ _ Harg)
    case appr₂ =>
      cases Hτ
      case app₂ Hf HX =>
        have ⟨τ𝕖, Hsem𝕖, HsemX⟩ := IH _ _ HX
        exists τ𝕖
        constructor; apply Hsem𝕖
        apply compatibility.app
        apply typing.erase.fundamental _ _ _ _ _ (typing.weakening.singleton _ _ _ _ _ _ _ Hf)
        apply HsemX
    case lift =>
      cases Hτ
      case lift_lam τ𝕒 τ𝕓 _ _ HX =>
        apply IH (.arrow (.fragment τ𝕒) (.fragment τ𝕓) _); apply HX
      case lift_lit HX =>
        apply IH .nat; apply HX
    case lets e _ =>
      cases Hτ
      case lets HX Hclose He =>
        have ⟨τ𝕖, Hsem𝕖, HsemX⟩ := IH _ _ HX
        exists τ𝕖
        constructor; apply Hsem𝕖
        apply compatibility.lets
        . constructor
          . rw [← env.erase.length, ← closed.under_erase]
            apply closed.under_ctx𝔼; apply HE
            apply closed.inc; apply typing.closed_at_env; apply HX; simp; simp
          . rw [← env.erase.length, ← closed.under_erase]
            apply closed.inc; apply Hclose; simp
        . constructor
          . rw [← env.erase.length, ← closed.under_erase]
            apply closed.under_ctx𝔼; apply HE
            apply closed.inc; apply typing.closed_at_env; apply HX; simp; simp
          . rw [← env.erase.length, ← closed.under_erase]
            apply closed.inc; apply Hclose; simp
        . apply HsemX
        . rw [← env.erase, ← comm.erase_opening]
          apply typing.erase.fundamental
          rw [← List.singleton_append, List.append_cons, ← env.erase.length]
          have HEq : ({0 ↦ ((τ𝕖, 𝟙) :: Γ).length} e) = shiftl_at Γ.length [(τ𝕖, 𝟙)].length ({0 ↦ Γ.length} e) :=
            by
            rw [comm.shiftl_opening, identity.shiftl]; rfl
            apply Hclose; rfl
          rw [HEq]; apply typing.weakening.strengthened; apply He; rfl
