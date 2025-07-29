import CollapsingTowers.TwoLevelBasic.SyntacticTyping.PresvCtx
import CollapsingTowers.TwoLevelBasic.Semantic.Defs

lemma typing.pure_under_ctx𝔹 :
  ∀ Γ B e τ φ,
    ctx𝔹 B →
    φ = ∅ →
    typing Γ 𝟙 B⟦e⟧ τ φ →
    ∃ τ, typing Γ 𝟙 e τ ∅  :=
  by
  intros Γ B e τ φ HB HEqφ Hτ
  cases HB <;> try (cases Hτ <;> contradiction)
  case appl₁ =>
    cases Hτ
    case app₁ φ₀ φ₁ φ₂ IHarg IHf =>
      cases φ₀ <;> cases φ₁ <;> cases φ₂ <;> try contradiction
      constructor; apply IHf
  case appr₁ =>
    cases Hτ
    case app₁ φ₀ φ₁ φ₂ IHarg IHf =>
      cases φ₀ <;> cases φ₁ <;> cases φ₂ <;> try contradiction
      constructor; apply IHarg
  case lets =>
    cases Hτ
    case lets φ₀ φ₁ HwellBinds IHb Hclose IHe =>
      cases φ₀ <;> cases φ₁ <;> try contradiction
      constructor; apply IHb

lemma preservation.reflect :
  ∀ Γ E e τ φ,
    ctx𝔼 E →
    typing_reification Γ (E (.reflect e)) τ φ →
    typing_reification Γ (.lets𝕔 e (E (.code (.bvar 0)))) τ ∅ :=
  by
  intros Γ E e τ φ HE Hτ
  cases Hτ
  case pure Hτ =>
    exfalso
    induction HE generalizing τ with
    | hole => nomatch Hτ
    | cons𝔹 _ _ HB _ IH =>
      have ⟨_, Hτ⟩ := typing.pure_under_ctx𝔹 _ _ _ _ _ HB rfl Hτ
      apply IH; apply Hτ
  case reify τ Hτ =>
    have ⟨τ𝕖, φ₀, φ₁, HEqφ, Hτr, HτE⟩ := preservation.under_ctx𝔼 _ _ _ _ _ HE Hτ
    cases Hτr with
    | reflect _ _ _ Hτe =>
      have ⟨HwellBinds, _⟩ := typing.dyn_impl_pure _ _ _ _ Hτe
      apply typing_reification.pure
      apply typing.lets𝕔; apply Hτe
      apply typing_reification.reify
      rw [opening.under_ctx𝔼 _ _ _ _ HE, ← List.singleton_append]
      apply HτE; apply typing.code_fragment; simp
      apply HwellBinds
      apply HwellBinds
      apply closed.under_ctx𝔼; apply HE
      apply typing.closed_at_env; apply Hτ; simp

lemma preservation.under_ctxℚ :
  ∀ Γ Q E e τ φ,
    ctxℚ Γ.length Q →
    ctx𝔼 E →
    lc e →
    typing Γ 𝟙 (Q (E (.reflect e))) τ φ →
    typing Γ 𝟙 (Q (.lets𝕔 e (E (.code (.bvar 0))))) τ φ :=
  by
  intros Γ Q E e τ φ HQ HE Hlc Hτ
  generalize HEqlvl : Γ.length = lvl
  rw [HEqlvl] at HQ
  induction HQ generalizing τ φ Γ with
  | holeℝ _ HR =>
    cases HR
    case lam𝕔 =>
      rw [← HEqlvl] at Hτ; rw [← HEqlvl]
      cases Hτ
      case lam𝕔 HwellBinds IHe Hclose =>
        rw [identity.opening_closing] at IHe
        apply typing.lam𝕔; rw [identity.opening_closing]
        apply preservation.reflect; apply HE; apply IHe
        constructor; apply Hlc
        apply lc.under_ctx𝔼; apply HE; simp
        apply HwellBinds
        rw [← closed.under_closing]; constructor
        apply closed.decompose_ctx𝔼 _ (.reflect e) _ HE
        rw [← List.length_cons]; apply typing_reification.closed_at_env; apply IHe
        apply closed.under_ctx𝔼; apply HE
        rw [← List.length_cons]; apply typing_reification.closed_at_env; apply IHe; simp
        apply lc.under_ctx𝔼; apply HE; apply Hlc
    case lets𝕔 =>
      rw [← HEqlvl] at Hτ; rw [← HEqlvl]
      cases Hτ
      case lets𝕔 HwellBinds IHb IHe Hclose =>
        rw [identity.opening_closing] at IHe
        apply typing.lets𝕔; apply IHb; rw [identity.opening_closing]
        apply preservation.reflect; apply HE; apply IHe
        constructor; apply Hlc
        apply lc.under_ctx𝔼; apply HE; simp
        apply HwellBinds
        rw [← closed.under_closing]; constructor
        apply closed.decompose_ctx𝔼 _ (.reflect e) _ HE
        rw [← List.length_cons]; apply typing_reification.closed_at_env; apply IHe
        apply closed.under_ctx𝔼; apply HE
        rw [← List.length_cons]; apply typing_reification.closed_at_env; apply IHe; simp
        apply lc.under_ctx𝔼; apply HE; apply Hlc
    case run =>
      cases Hτ
      case run Hclose IH =>
        apply typing.run
        apply preservation.reflect
        apply HE; apply IH
        constructor
        apply closed.decompose_ctx𝔼 _ (.reflect e) _ HE
        apply Hclose
        apply closed.under_ctx𝔼; apply HE; apply Hclose; simp
  | cons𝔹 _ _ HB _ IHQ =>
    simp; apply preservation.under_ctx𝔹
    apply HB; intros _ _ IHτ
    apply IHQ; apply IHτ; apply HEqlvl; apply Hτ
  | consℝ R Q HR HQ IHQ =>
    simp; apply preservation.under_ctxℝ _ _ _ (Q (E (.reflect e)))
    rw [HEqlvl]; apply HR
    apply lc.under_ctxℚ; apply HQ
    apply lc.under_ctx𝔼; apply HE
    apply Hlc
    . intros _ _ _ _ IHτ
      apply IHQ; apply IHτ; simp; omega;
    . apply fv.under_ctxℚ; apply HQ
      simp; constructor
      have H : fv e = fv (.reflect e) := rfl; rw [H]
      apply fv.decompose_ctx𝔼; apply HE
      apply fv.under_ctx𝔼; apply HE; simp
    apply Hτ
