import CollapsingTowers.TwoLvLBasic.SyntacticTyping.Typing
import CollapsingTowers.TwoLvLBasic.Semantic.Defs

@[simp]
def dyn_env (Γ : TEnv) : Prop :=
  ∀ x τ 𝕊, binds x (τ, 𝕊) Γ → ¬𝕊 = .stat

lemma dyn_env.extend :
  ∀ Γ τ,
    dyn_env Γ →
    dyn_env ((τ, .dyn) :: Γ) :=
  by
  intros Γ τ₀ HDyn x τ₁ 𝕊 Hbinds HEq𝕊
  simp at Hbinds; rw [HEq𝕊] at Hbinds
  by_cases HEqx : (Γ.length = x)
  . rw [if_pos HEqx] at Hbinds
    nomatch Hbinds
  . rw [if_neg HEqx] at Hbinds
    apply HDyn; apply Hbinds; rfl

theorem progress.strengthened :
  ∀ Γ e₀ τ φ,
    typing_reification Γ e₀ τ φ →
    dyn_env Γ →
    value e₀ ∨ ∃ e₁, step_lvl Γ.length e₀ e₁ :=
  by
  intros Γ e₀ τ φ Hτ
  apply @typing_reification.rec
    (fun Γ 𝕊 e₀ τ φ (H : typing Γ 𝕊 e₀ τ φ) =>
      dyn_env Γ →
      𝕊 = .stat →
      value e₀ ∨ ∃ e₁, step_lvl Γ.length e₀ e₁)
    (fun Γ e₀ τ φ (H : typing_reification Γ e₀ τ φ) =>
      dyn_env Γ →
      value e₀ ∨ ∃ e₁, step_lvl Γ.length e₀ e₁)
  <;> intros
  case fvar x _ Hbinds HwellBinds HDyn HEq𝕊 =>
    exfalso; apply HDyn; apply Hbinds; apply HEq𝕊
  case lam H HwellBinds Hclose IH HDyn HEq𝕊 =>
    left; apply value.lam
    apply (lc.under_opening _ _ _).mp; apply typing.regular; apply H
  case lift_lam H IH HDyn HEq𝕊 =>
    right
    cases IH HDyn rfl with
    | inl Hvalue =>
      cases Hvalue with
      | lam e Hlc =>
        exists .lam𝕔 (maping𝕔 0 e)
        apply step_lvl.pure _ _ _ ctx𝕄.hole
        apply Hlc; apply head.lift_lam
      | _ => nomatch H
    | inr Hstep =>
      have ⟨_, Hstep⟩ := Hstep
      apply step.congruence_under_ctx𝔹 _ _ _ _ ctx𝔹.lift; apply Hstep
  case app₁ e₀ e₁ _ _ _ _ _ H₀ H₁ IH₀ IH₁ HDyn HEq𝕊 =>
    right
    cases IH₀ HDyn HEq𝕊 with
    | inl Hvalue₀ =>
      cases IH₁ HDyn HEq𝕊 with
      | inl Hvalue₁ =>
        cases Hvalue₀ with
        | lam e₀ Hlc₀ =>
          exists opening 0 e₁ e₀
          apply step_lvl.pure _ _ _ ctx𝕄.hole
          constructor; apply Hlc₀; apply value_impl_lc; apply Hvalue₁
          apply head.app₁; apply Hvalue₁
        | _ => nomatch H₀
      | inr Hstep₁ =>
        have ⟨_, Hstep₁⟩ := Hstep₁
        apply step.congruence_under_ctx𝔹 _ _ _ _ (ctx𝔹.appr₁ _ _); apply Hstep₁
        apply Hvalue₀
    | inr Hstep₀ =>
      have ⟨_, Hstep₀⟩ := Hstep₀
      apply step.congruence_under_ctx𝔹 _ _ _ _ (ctx𝔹.appl₁ _ _); apply Hstep₀
      apply typing.regular; apply H₁
  case app₂ e₀ e₁ _ _ _ _ H₀ H₁ IH₀ IH₁ HDyn HEq𝕊 =>
    right
    cases IH₀ HDyn HEq𝕊 with
    | inl Hvalue₀ =>
      cases IH₁ HDyn HEq𝕊 with
      | inl Hvalue₁ =>
        cases Hvalue₀ with
        | code e₀ Hlc₀ =>
          cases Hvalue₁ with
          | code e₁ Hlc₁ =>
            exists .reflect (.app₁ e₀ e₁)
            apply step_lvl.pure _ _ _ ctx𝕄.hole
            constructor; apply Hlc₀; apply Hlc₁
            apply head.app₂
          | _ => nomatch H₁
        | _ => nomatch H₀
      | inr Hstep₁ =>
        have ⟨_, Hstep₁⟩ := Hstep₁
        apply step.congruence_under_ctx𝔹 _ _ _ _ (ctx𝔹.appr₂ _ _); apply Hstep₁
        apply Hvalue₀
    | inr Hstep₀ =>
      have ⟨_, Hstep₀⟩ := Hstep₀
      apply step.congruence_under_ctx𝔹 _ _ _ _ (ctx𝔹.appl₂ _ _); apply Hstep₀
      apply typing.regular; apply H₁
  case lit => left; apply value.lit
  case lift_lit H IH HDyn HEq𝕊 =>
    right
    cases IH HDyn HEq𝕊 with
    | inl Hvalue =>
      cases Hvalue with
      | lit e =>
        exists .reflect (.lit e)
        apply step_lvl.pure _ _ _ ctx𝕄.hole
        simp; apply head.lift_lit
      | _ => nomatch H
    | inr Hstep =>
      have ⟨_, Hstep⟩ := Hstep
      apply step.congruence_under_ctx𝔹 _ _ _ _ ctx𝔹.lift; apply Hstep
  case code_fragment => left; apply value.code; simp
  case code_rep H IH HDyn HEq𝕊 =>
    left; apply value.code
    apply typing.regular; apply H
  case reflect e _ H _ _ _ =>
    right; exists .lets𝕔 e (.code (.bvar 0))
    apply step_lvl.reflect _ _ _ ctxℙ.hole ctx𝔼.hole
    apply typing.regular; apply H
  case lam𝕔 Γ e _ _ _ H HwellBinds Hclose IH HDyn HEq𝕊 =>
    right
    rw [← identity.closing_opening _ e _ Hclose]
    cases IH (dyn_env.extend _ _ HDyn) with
    | inl Hvalue =>
      generalize HEqe : ({0 ↦ Γ.length} e) = e𝕠
      rw [HEqe] at Hvalue H
      cases Hvalue with
      | code e Hlc =>
        exists .reflect (.lam ({0 ↤ Γ.length} e))
        apply step_lvl.pure _ _ _ ctx𝕄.hole
        apply lc.under_closing; omega
        apply lc.inc; apply Hlc; omega
        apply head.lam𝕔
      | _ => contradiction
    | inr Hstep =>
      have ⟨_, Hstep⟩ := Hstep
      constructor
      apply step.congruence_under_ctxℝ _ _ _ _ _ ctxℝ.lam𝕔; apply Hstep
  case lets e₀ e₁ _ _ _ _ H₀ H₁ _ _ IH₀ IH₁ HDyn HEq𝕊 =>
    right
    cases IH₀ HDyn HEq𝕊 with
    | inl Hvalue₀ =>
      exists opening 0 e₀ e₁
      apply step_lvl.pure _ _ _ ctx𝕄.hole
      constructor
      apply value_impl_lc; apply Hvalue₀
      apply (lc.under_opening _ _ _).mp; apply typing.regular; apply H₁
      apply head.lets; apply Hvalue₀
    | inr Hstep₀ =>
      have ⟨_, Hstep₀⟩ := Hstep₀
      apply step.congruence_under_ctx𝔹 _ _ _ _ (ctx𝔹.lets _ _); apply Hstep₀
      apply (lc.under_opening _ _ _).mp; apply typing.regular; apply H₁
  case lets𝕔 Γ b e _ _ _ H₀ H₁ HwellBinds Hclose _ IH₁ HDyn HEq𝕊 =>
    right
    rw [← identity.closing_opening _ e _ Hclose]
    cases IH₁ (dyn_env.extend _ _ HDyn) with
    | inl Hvalue =>
      generalize HEqe : ({0 ↦ Γ.length} e) = e𝕠
      rw [HEqe] at Hvalue H₁
      cases Hvalue with
      | code e Hlc =>
        exists .code (.lets b ({0 ↤ Γ.length} e))
        apply step_lvl.pure _ _ _ ctx𝕄.hole
        constructor
        apply typing.regular; apply H₀
        apply lc.under_closing; omega
        apply lc.inc; apply Hlc; omega
        apply head.lets𝕔
      | _ => contradiction
    | inr Hstep =>
      have ⟨_, Hstep⟩ := Hstep
      constructor
      apply step.congruence_under_ctxℝ _ _ _ _ _ (ctxℝ.lets𝕔 _ _); apply Hstep
      apply typing.regular; apply H₀
  case run Hclose IH HDyn HEq𝕊 =>
    right
    cases IH HDyn with
    | inl Hvalue =>
      cases Hvalue with
      | code e Hlc =>
        exists e
        apply step_lvl.pure _ _ _ ctx𝕄.hole
        apply Hlc
        apply head.run
      | _ => contradiction
    | inr Hstep =>
      have ⟨_, Hstep⟩ := Hstep
      constructor
      apply step.congruence_under_ctxℝ _ _ _ _ _ ctxℝ.run; apply Hstep
  case pure IH HDyn =>
    apply IH; apply HDyn; rfl
  case reify IH HDyn =>
    apply IH; apply HDyn; rfl
  apply Hτ

theorem progress :
  ∀ e₀ τ φ,
    typing_reification [] e₀ τ φ →
    value e₀ ∨ ∃ e₁, (e₀ ⇝ e₁) :=
  by
  intros _ _ _ Hτ
  apply progress.strengthened []
  apply Hτ; simp
