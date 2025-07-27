import Mathlib.Tactic.ApplyAt
import CollapsingTowers.TwoLvLBasic.SyntacticTyping.Typing
import CollapsingTowers.TwoLvLBasic.Semantic.Defs

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
    case lets HwellBinds IHb Hclose IHe =>
      apply typing.lets
      apply IH; apply IHb; apply IHe
      apply HwellBinds; apply Hclose

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
    case lam𝕔 HwellBinds IHe Hclose =>
      rw [identity.opening_closing] at IHe
      . cases IHe with
        | pure _ _ _ IHe₀ =>
          rw [← List.singleton_append] at IHe₀
          apply IH at IHe₀
          apply typing.lam𝕔
          apply typing_reification.pure
          rw [identity.opening_closing]
          apply IHe₀; apply typing.regular; apply IHe₀
          apply HwellBinds
          rw [← closed.under_closing, ← List.length_cons]
          apply typing.closed_at_env; apply IHe₀; rfl
        | reify _ _ _ _ IHe₀ =>
          rw [← List.singleton_append] at IHe₀
          apply IH at IHe₀
          apply typing.lam𝕔
          apply typing_reification.reify
          rw [identity.opening_closing]
          apply IHe₀; apply typing.regular; apply IHe₀
          apply HwellBinds
          rw [← closed.under_closing, ← List.length_cons]
          apply typing.closed_at_env; apply IHe₀; rfl
      apply Hlc
  case lets𝕔 =>
    cases Hτ
    case lets𝕔 HwellBinds IHb IHe Hclose =>
      rw [identity.opening_closing] at IHe
      . cases IHe with
        | pure _ _ _ IHe₀ =>
          rw [← List.singleton_append] at IHe₀
          apply IH at IHe₀
          apply typing.lets𝕔; apply IHb
          apply typing_reification.pure
          rw [identity.opening_closing]
          apply IHe₀; apply typing.regular; apply IHe₀
          apply HwellBinds
          rw [← closed.under_closing, ← List.length_cons]
          apply typing.closed_at_env; apply IHe₀; rfl
        | reify _ _ _ _ IHe₀ =>
          rw [← List.singleton_append] at IHe₀
          apply IH at IHe₀
          apply typing.lets𝕔; apply IHb
          apply typing_reification.reify
          rw [identity.opening_closing]
          apply IHe₀; apply typing.regular; apply IHe₀
          apply HwellBinds
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
