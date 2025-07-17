
import CollapsingTowers.TwoLevelBasic.Typing
import CollapsingTowers.TwoLevelBasic.Preservation.Ctx
theorem pure𝔹 :
  ∀ Γ B e τ φ,
    ctx𝔹 B →
    φ = ∅ →
    typing Γ Stage.stat (B e) τ φ →
    ∃ τ, typing Γ Stage.stat e τ ∅  :=
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

theorem preservation_reflect :
  ∀ Γ E e τ φ,
    ctx𝔼 E →
    typing_reification Γ (E (.reflect e)) τ φ →
    typing_reification Γ (.let𝕔 e (E (.code (.bvar 0)))) τ ∅ :=
  by
  intros Γ E e τ φ HE Hτ
  cases Hτ
  case pure Hτ =>
    exfalso
    induction HE generalizing τ with
    | hole => nomatch Hτ
    | cons𝔹 _ _ HB _ IH =>
      have ⟨_, Hτ⟩ := pure𝔹 _ _ _ _ _ HB rfl Hτ
      apply IH; apply Hτ
  case reify τ Hτ =>
    have ⟨τ𝕖, φ₀, φ₁, HEqφ, Hτr, HτE⟩ := decompose𝔼 _ _ _ _ _ HE Hτ
    cases Hτr with
    | reflect _ _ _ Hτe =>
      have ⟨HwellBinds, _⟩ := typing_dyn_pure _ _ _ _ Hτe
      apply typing_reification.pure
      apply typing.let𝕔; apply Hτe
      apply typing_reification.reify
      rw [open_ctx𝔼_map _ _ _ HE, ← List.singleton_append]
      apply HτE; apply typing.code_fragment; simp
      apply HwellBinds
      apply HwellBinds
      apply closed_at𝔼; apply HE
      apply typing_closed; apply Hτ; simp

theorem decomposeℚ_reflect :
  ∀ Γ Q E e τ φ,
    ctxℚ Γ.length Q →
    ctx𝔼 E →
    lc e →
    typing Γ .stat (Q (E (.reflect e))) τ φ →
    typing Γ .stat (Q (.let𝕔 e (E (.code (.bvar 0))))) τ φ :=
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
        rw [open_close_id₀] at IHe
        apply typing.lam𝕔; rw [open_close_id₀]
        apply preservation_reflect; apply HE; apply IHe
        constructor; apply Hlc
        apply lc_ctx𝔼; apply HE; simp
        apply HwellBinds
        apply (close_closed _ _ _).mp; constructor
        apply closed_at_decompose𝔼 _ (.reflect e) _ HE
        rw [← List.length_cons]; apply typing_reification_closed; apply IHe
        apply closed_at𝔼; apply HE
        rw [← List.length_cons]; apply typing_reification_closed; apply IHe; simp
        apply lc_ctx𝔼; apply HE; apply Hlc
    case let𝕔 =>
      rw [← HEqlvl] at Hτ; rw [← HEqlvl]
      cases Hτ
      case let𝕔 HwellBinds IHb IHe Hclose =>
        rw [open_close_id₀] at IHe
        apply typing.let𝕔; apply IHb; rw [open_close_id₀]
        apply preservation_reflect; apply HE; apply IHe
        constructor; apply Hlc
        apply lc_ctx𝔼; apply HE; simp
        apply HwellBinds
        apply (close_closed _ _ _).mp; constructor
        apply closed_at_decompose𝔼 _ (.reflect e) _ HE
        rw [← List.length_cons]; apply typing_reification_closed; apply IHe
        apply closed_at𝔼; apply HE
        rw [← List.length_cons]; apply typing_reification_closed; apply IHe; simp
        apply lc_ctx𝔼; apply HE; apply Hlc
    case run =>
      cases Hτ
      case run Hclose IH =>
        apply typing.run
        apply preservation_reflect
        apply HE; apply IH
        constructor
        apply closed_at_decompose𝔼 _ (.reflect e) _ HE
        apply Hclose
        apply closed_at𝔼; apply HE; apply Hclose; simp
  | cons𝔹 _ _ HB _ IHQ =>
    simp; apply decompose𝔹
    apply HB; intros _ _ IHτ
    apply IHQ; apply IHτ; apply HEqlvl; apply Hτ
  | consℝ R Q HR HQ IHQ =>
    simp; apply decomposeℝ _ _ _ (Q (E (.reflect e)))
    rw [HEqlvl]; apply HR
    apply lc_ctxℚ; apply HQ
    apply lc_ctx𝔼; apply HE
    apply Hlc
    . intros _ _ _ _ IHτ
      apply IHQ; apply IHτ; simp; omega;
    . apply fv_atℚ; apply HQ
      simp; constructor
      have H : fv e = fv (.reflect e) := rfl; rw [H]
      apply fv_decompose𝔼; apply HE
      apply fv_at𝔼; apply HE; simp
    apply Hτ
