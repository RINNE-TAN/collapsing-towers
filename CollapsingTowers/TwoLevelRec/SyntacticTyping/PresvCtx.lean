import Mathlib.Tactic.ApplyAt
import CollapsingTowers.TwoLevelRec.SyntacticTyping.Weakening
import CollapsingTowers.TwoLevelRec.Semantic.Defs

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
    case app₁ IHarg IHf =>
      apply typing.app₁
      apply IH; apply IHf; apply IHarg
  case appr₁ =>
    cases Hτ
    case app₁ IHarg IHf =>
      apply typing.app₁
      apply IHf; apply IH; apply IHarg
  case appl₂ =>
    cases Hτ
    case app₂ IHf IHarg =>
      apply typing.app₂
      apply IH; apply IHf; apply IHarg
  case appr₂ =>
    cases Hτ
    case app₂ IHf IHarg =>
      apply typing.app₂
      apply IHf; apply IH; apply IHarg
  case lift =>
    cases Hτ
    case lift_lit IHn =>
      apply typing.lift_lit
      apply IH; apply IHn
    case lift_lam IHe =>
      apply typing.lift_lam
      apply IH; apply IHe
  case lets =>
    cases Hτ
    case lets Hwbt IHb Hclose IHe =>
      apply typing.lets
      apply IH; apply IHb; apply IHe
      apply Hwbt; apply Hclose
  case fix₁ =>
    cases Hτ
    case fix₁ Hfixφ Hτ =>
      apply typing.fix₁; apply Hfixφ
      apply IH; apply Hτ
  case fix₂ =>
    cases Hτ
    case fix₂ Hτ =>
      apply typing.fix₂
      apply IH; apply Hτ

lemma preservation.under_ctxℝ :
  ∀ intro Γ R e₀ e₁ τ φ,
    ctxℝ intro Γ.length R →
    lc e₀ →
    (∀ Δ τ φ,
      Δ.length = intro →
      typing (Δ ++ Γ) 𝟙 e₀ τ φ →
      typing (Δ ++ Γ) 𝟙 e₁ τ φ
    ) →
    fv e₁ ⊆ fv e₀ →
    typing Γ 𝟙 R⟦e₀⟧ τ φ →
    typing Γ 𝟙 R⟦e₁⟧ τ φ :=
  by
  intros intro Γ R e₀ e₁ τ φ HR Hlc IH Hsubst Hτ
  cases HR
  case lam𝕔 =>
    cases Hτ
    case lam𝕔 Hwbt IHe Hclose =>
      rw [identity.opening_closing] at IHe
      . cases IHe with
        | pure _ _ _ IHe₀ =>
          rw [← List.singleton_append] at IHe₀
          apply IH at IHe₀
          apply typing.lam𝕔
          apply typing_reification.pure
          rw [identity.opening_closing]
          apply IHe₀; apply typing.regular; apply IHe₀
          apply Hwbt
          rw [← closed.under_closing, ← List.length_cons]
          apply typing.closed_at_env; apply IHe₀; rfl
        | reify _ _ _ _ IHe₀ =>
          rw [← List.singleton_append] at IHe₀
          apply IH at IHe₀
          apply typing.lam𝕔
          apply typing_reification.reify
          rw [identity.opening_closing]
          apply IHe₀; apply typing.regular; apply IHe₀
          apply Hwbt
          rw [← closed.under_closing, ← List.length_cons]
          apply typing.closed_at_env; apply IHe₀; rfl
      apply Hlc
  case lets𝕔 =>
    cases Hτ
    case lets𝕔 Hwbt IHb IHe Hclose =>
      rw [identity.opening_closing] at IHe
      . cases IHe with
        | pure _ _ _ IHe₀ =>
          rw [← List.singleton_append] at IHe₀
          apply IH at IHe₀
          apply typing.lets𝕔; apply IHb
          apply typing_reification.pure
          rw [identity.opening_closing]
          apply IHe₀; apply typing.regular; apply IHe₀
          apply Hwbt
          rw [← closed.under_closing, ← List.length_cons]
          apply typing.closed_at_env; apply IHe₀; rfl
        | reify _ _ _ _ IHe₀ =>
          rw [← List.singleton_append] at IHe₀
          apply IH at IHe₀
          apply typing.lets𝕔; apply IHb
          apply typing_reification.reify
          rw [identity.opening_closing]
          apply IHe₀; apply typing.regular; apply IHe₀
          apply Hwbt
          rw [← closed.under_closing, ← List.length_cons]
          apply typing.closed_at_env; apply IHe₀; rfl
      apply Hlc
  case run =>
    cases Hτ
    case run Hclose Hτ =>
      cases Hτ with
      | pure _ _ _ Hτ =>
        apply typing.run
        apply typing_reification.pure
        rw [← List.nil_append Γ]
        apply IH; simp; apply Hτ
        rw [closed_iff_fv_empty]
        rw [closed_iff_fv_empty] at Hclose
        rw [Hclose] at Hsubst
        simp at Hsubst; apply Hsubst
      | reify _ _ _ _ Hτ =>
        apply typing.run
        apply typing_reification.reify
        rw [← List.nil_append Γ]
        apply IH; simp; apply Hτ
        rw [closed_iff_fv_empty]
        rw [closed_iff_fv_empty] at Hclose
        rw [Hclose] at Hsubst
        simp at Hsubst; apply Hsubst

lemma preservation.under_ctx𝕄 :
  ∀ Γ M e₀ e₁ τ φ,
    ctx𝕄 Γ.length M →
    lc e₀ →
    fv e₁ ⊆ fv e₀ →
    (∀ Γ τ φ,
      typing Γ 𝟙 e₀ τ φ →
      typing Γ 𝟙 e₁ τ φ
    ) →
    typing Γ 𝟙 M⟦e₀⟧ τ φ →
    typing Γ 𝟙 M⟦e₁⟧ τ φ :=
  by
  intros Γ M e₀ e₁ τ φ HM Hlc HFv IH Hτ
  generalize HEqlvl : Γ.length = lvl
  rw [HEqlvl] at HM
  induction HM generalizing τ φ Γ with
  | hole => apply IH; apply Hτ
  | cons𝔹 _ _ HB _ IHM =>
    simp; apply preservation.under_ctx𝔹
    apply HB; intros _ _ IHτ
    apply IHM; apply IHτ; apply HEqlvl; apply Hτ
  | consℝ _ _ HR HM IHM =>
    simp; apply preservation.under_ctxℝ
    rw [HEqlvl]; apply HR
    apply lc.under_ctx𝕄
    apply HM; apply Hlc
    . intros _ _ _ _ IHτ
      apply IHM; apply IHτ; simp; omega
    . apply fv.under_ctx𝕄; apply HM
      apply HFv
    apply Hτ

lemma preservation.under_ctx𝔼 :
  ∀ Γ E e τ φ,
    ctx𝔼 E →
    typing Γ 𝟙 (E e) τ φ →
    ∃ τ𝕖 φ𝕖 φ𝔼,
      φ = φ𝕖 ∪ φ𝔼 ∧
      typing Γ 𝟙 e τ𝕖 φ𝕖 ∧
      ∀ e φ Δ,
        typing (Δ ++ Γ) 𝟙 e τ𝕖 φ →
        typing (Δ ++ Γ) 𝟙 (E e) τ (φ ∪ φ𝔼) :=
  by
  intros Γ E e τ φ HE Hτ
  induction HE generalizing φ τ with
  | hole =>
    exists τ, φ, ∅
    constructor; cases φ <;> rfl
    constructor; apply Hτ
    intros e φ Δ Hτ; cases φ <;> apply Hτ
  | cons𝔹 _ _ HB _ IH =>
    cases HB
    case appl₁ =>
      cases Hτ
      case app₁ φ₀ φ₁ φ₂ Harg HX =>
        have ⟨τ𝕖, φ𝕖, φ𝔼, HEqφ, He, IH⟩ := IH _ _ HX
        exists τ𝕖, φ𝕖, (φ₀ ∪ φ𝔼 ∪ φ₂)
        constructor
        . rw [HEqφ]
          cases φ₀ <;> cases φ₂ <;>
          cases φ𝕖 <;> cases φ𝔼 <;> simp
        . constructor; apply He
          intros e φ Δ He
          have HEqφ : (φ ∪ (φ₀ ∪ φ𝔼 ∪ φ₂)) = φ₀ ∪ (φ ∪ φ𝔼) ∪ φ₂ :=
            by
            cases φ₀ <;> cases φ₂ <;>
            cases φ <;> cases φ𝔼 <;> simp
          rw [HEqφ]
          apply typing.app₁
          apply IH; apply He
          apply typing.weakening; apply Harg
    case appr₁ =>
      cases Hτ
      case app₁ φ₀ φ₁ φ₂ HX Hf =>
        have ⟨τ𝕖, φ𝕖, φ𝔼, HEqφ, He, IH⟩ := IH _ _ HX
        exists τ𝕖, φ𝕖, (φ₀ ∪ φ₁ ∪ φ𝔼)
        constructor
        . rw [HEqφ]
          cases φ₀ <;> cases φ₁ <;>
          cases φ𝕖 <;> cases φ𝔼 <;> simp
        . constructor; apply He
          intros e φ Δ He
          have HEqφ : (φ ∪ (φ₀ ∪ φ₁ ∪ φ𝔼)) = φ₀ ∪ φ₁ ∪ (φ ∪ φ𝔼) :=
            by
            cases φ₀ <;> cases φ₁ <;>
            cases φ <;> cases φ𝔼 <;> simp
          rw [HEqφ]
          apply typing.app₁
          apply typing.weakening; apply Hf
          apply IH; apply He
    case appl₂ =>
      cases Hτ
      case app₂ φ₀ φ₁ HX Harg =>
        have ⟨τ𝕖, φ𝕖, φ𝔼, HEqφ, He, IH⟩ := IH _ _ HX
        exists τ𝕖, φ𝕖, .reify
        constructor
        . cases φ𝕖 <;> simp
        . constructor; apply He
          intros e φ Δ He
          have HEqφ : (φ ∪ .reify) = .reify :=
            by cases φ <;> simp
          rw [HEqφ]
          apply typing.app₂
          apply IH; apply He
          apply typing.weakening; apply Harg
    case appr₂ =>
      cases Hτ
      case app₂ φ₀ φ₁ Hf HX =>
        have ⟨τ𝕖, φ𝕖, φ𝔼, HEqφ, He, IH⟩ := IH _ _ HX
        exists τ𝕖, φ𝕖, .reify
        constructor
        . cases φ𝕖 <;> simp
        . constructor; apply He
          intros e φ Δ He
          have HEqφ : (φ ∪ .reify) = .reify :=
            by cases φ <;> simp
          rw [HEqφ]
          apply typing.app₂
          apply typing.weakening; apply Hf
          apply IH; apply He
    case lift =>
      cases Hτ
      case lift_lit HX =>
        have ⟨τ𝕖, φ𝕖, φ𝔼, HEqφ, He, IH⟩ := IH _ _ HX
        exists τ𝕖, φ𝕖, .reify
        constructor
        . cases φ𝕖 <;> simp
        . constructor; apply He
          intros e φ Δ He
          have HEqφ : (φ ∪ .reify) = .reify :=
            by cases φ <;> simp
          rw [HEqφ]
          apply typing.lift_lit
          apply IH; apply He
      case lift_lam HX =>
        have ⟨τ𝕖, φ𝕖, φ𝔼, HEqφ, He, IH⟩ := IH _ _ HX
        exists τ𝕖, φ𝕖, .reify
        constructor
        . cases φ𝕖 <;> simp
        . constructor; apply He
          intros e φ Δ He
          have HEqφ : (φ ∪ .reify) = .reify :=
            by cases φ <;> simp
          rw [HEqφ]
          apply typing.lift_lam
          apply IH; apply He
    case lets =>
      cases Hτ
      case lets body _ _ φ₀ φ₁ Hwbt HX Hclose Hbody =>
        have ⟨τ𝕖, φ𝕖, φ𝔼, HEqφ, He, IH⟩ := IH _ _ HX
        exists τ𝕖, φ𝕖, (φ₁ ∪ φ𝔼)
        constructor
        . rw [HEqφ]
          cases φ₁ <;> cases φ𝕖 <;> cases φ𝔼 <;> simp
        . constructor; apply He
          intros e φ Δ He
          have HEqφ : (φ ∪ (φ₁ ∪ φ𝔼)) = ((φ ∪ φ𝔼) ∪ φ₁) :=
            by cases φ₁ <;> cases φ <;> cases φ𝔼 <;> simp
          rw [HEqφ]
          apply typing.lets
          apply IH; apply He
          rw [← identity.shiftl Γ.length body Δ.length]
          rw [← List.singleton_append, ← List.append_assoc]
          rw [List.length_append, Nat.add_comm, ← comm.shiftl_opening]
          apply typing.weakening.strengthened; apply Hbody; rfl; rfl
          apply Hclose; apply Hwbt
          apply closed.inc; apply Hclose; simp
    case fix₁ =>
      cases Hτ
      case fix₁ Hfixφ HX =>
        have ⟨τ𝕖, φ𝕖, φ𝔼, HEqφ, He, IH⟩ := IH _ _ HX
        exists τ𝕖, φ𝕖, φ𝔼
        constructor
        . rw [HEqφ]
        . constructor; apply He
          intros e φ Δ He
          apply typing.fix₁; apply Hfixφ
          apply IH; apply He
    case fix₂ =>
      cases Hτ
      case fix₂ HX =>
      have ⟨τ𝕖, φ𝕖, φ𝔼, HEqφ, He, IH⟩ := IH _ _ HX
      exists τ𝕖, φ𝕖, .reify
      constructor
      . cases φ𝕖 <;> simp
      . constructor; apply He
        intros e φ Δ He
        have HEqφ : (φ ∪ .reify) = .reify :=
          by cases φ <;> simp
        rw [HEqφ]
        apply typing.fix₂
        apply IH; apply He
