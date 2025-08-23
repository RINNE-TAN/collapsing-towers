import CollapsingTowers.TwoLevelRec.SyntacticTyping.Defs
import CollapsingTowers.TwoLevelRec.OperationalSemantics.Defs

@[simp]
def dyn_env (Γ : TEnv) : Prop :=
  ∀ x τ 𝕊, binds x (τ, 𝕊) Γ → 𝕊 = 𝟚

lemma dyn_env.extend :
  ∀ Γ τ,
    dyn_env Γ →
    dyn_env ((τ, 𝟚) :: Γ) :=
  by
  intros Γ τ₀ HDyn x τ₁ 𝕊 Hbinds
  by_cases HEq : Γ.length = x
  . simp [if_pos HEq] at Hbinds
    simp [Hbinds]
  . simp [if_neg HEq] at Hbinds
    apply HDyn; apply Hbinds

theorem progress.strengthened :
  ∀ Γ e₀ τ φ,
    typing_reification Γ e₀ τ φ →
    dyn_env Γ →
    (∃ e₁, step_lvl Γ.length e₀ e₁) ∨ value e₀ :=
  by
  intros Γ e₀ τ φ Hτ
  apply @typing_reification.rec
    (fun Γ 𝕊 e₀ τ φ (H : typing Γ 𝕊 e₀ τ φ) =>
      dyn_env Γ → 𝕊 = 𝟙 → (∃ e₁, step_lvl Γ.length e₀ e₁) ∨ value e₀)
    (fun Γ e₀ τ φ (H : typing_reification Γ e₀ τ φ) =>
      dyn_env Γ → (∃ e₁, step_lvl Γ.length e₀ e₁) ∨ value e₀)
  <;> intros
  case fvar x _ HBinds Hwbt HDyn HEq𝕊 => simp [HDyn _ _ _ HBinds] at HEq𝕊
  case lam H Hwbt Hclosed IH HDyn HEq𝕊 => right; apply value.lam; simp; rw [← lc.under_opening]; apply typing.regular _ _ _ _ _ H
  case lit => right; apply value.lit
  case code_fragment => right; apply value.code; simp
  case code_rep H IH HDyn HEq𝕊 => right; apply value.code; apply typing.regular _ _ _ _ _ H
  case lift_lam H IH HDyn HEq𝕊 =>
    left
    match IH HDyn HEq𝕊 with
    | .inl Hstep =>
      have ⟨_, Hstep⟩ := Hstep
      apply step.congruence_under_ctx𝔹 _ _ _ _ ctx𝔹.lift Hstep
    | .inr Hvalue =>
      cases Hvalue <;> try contradiction
      case lam e Hlc =>
        exists .lam𝕔 (codify 0 e)
        apply step_lvl.pure _ _ _ ctx𝕄.hole
        . apply Hlc
        . apply head.lift_lam
  case app₁ e₀ e₁ _ _ _ _ _ H₀ H₁ IH₀ IH₁ HDyn HEq𝕊 =>
    left
    match IH₀ HDyn HEq𝕊, IH₁ HDyn HEq𝕊 with
    | .inl Hstep₀, _ =>
      have ⟨_, Hstep₀⟩ := Hstep₀
      apply step.congruence_under_ctx𝔹 _ _ _ _ (ctx𝔹.appl₁ _ _) Hstep₀
      apply typing.regular _ _ _ _ _ H₁
    | .inr Hvalue₀, .inl Hstep₁ =>
      have ⟨_, Hstep₁⟩ := Hstep₁
      apply step.congruence_under_ctx𝔹 _ _ _ _ (ctx𝔹.appr₁ _ _) Hstep₁
      apply Hvalue₀
    | .inr Hvalue₀, .inr Hvalue₁ =>
      cases Hvalue₀ <;> try contradiction
      case lam e₀ Hlc₀ =>
        exists opening 0 e₁ e₀
        apply step_lvl.pure _ _ _ ctx𝕄.hole
        . constructor; apply Hlc₀; apply lc.value _ Hvalue₁
        . apply head.app₁; apply Hvalue₁
  case app₂ e₀ e₁ _ _ _ _ H₀ H₁ IH₀ IH₁ HDyn HEq𝕊 =>
    left
    match IH₀ HDyn HEq𝕊, IH₁ HDyn HEq𝕊 with
    | .inl Hstep₀, _ =>
      have ⟨_, Hstep₀⟩ := Hstep₀
      apply step.congruence_under_ctx𝔹 _ _ _ _ (ctx𝔹.appl₂ _ _) Hstep₀
      apply typing.regular _ _ _ _ _ H₁
    | .inr Hvalue₀, .inl Hstep₁ =>
      have ⟨_, Hstep₁⟩ := Hstep₁
      apply step.congruence_under_ctx𝔹 _ _ _ _ (ctx𝔹.appr₂ _ _) Hstep₁
      apply Hvalue₀
    | .inr Hvalue₀, .inr Hvalue₁ =>
      cases Hvalue₀ <;> try contradiction
      case code e₀ Hlc₀ =>
      cases Hvalue₁ <;> try contradiction
      case code e₁ Hlc₁ =>
        exists .reflect (.app₁ e₀ e₁)
        apply step_lvl.pure _ _ _ ctx𝕄.hole
        . constructor; apply Hlc₀; apply Hlc₁
        . apply head.app₂
  case lift_lit H IH HDyn HEq𝕊 =>
    left
    match IH HDyn HEq𝕊 with
    | .inl Hstep =>
      have ⟨_, Hstep⟩ := Hstep
      apply step.congruence_under_ctx𝔹 _ _ _ _ ctx𝔹.lift Hstep
    | .inr Hvalue =>
      cases Hvalue <;> try contradiction
      case lit n =>
        exists .reflect (.lit n)
        apply step_lvl.pure _ _ _ ctx𝕄.hole
        . simp
        . apply head.lift_lit
  case binary₁ op _ _ _ _ H₀ H₁ IH₀ IH₁ HDyn HEq𝕊 =>
    left
    match IH₀ HDyn HEq𝕊, IH₁ HDyn HEq𝕊 with
    | .inl Hstep₀, _ =>
      have ⟨_, Hstep₀⟩ := Hstep₀
      apply step.congruence_under_ctx𝔹 _ _ _ _ (ctx𝔹.binaryl₁ _ _ _) Hstep₀
      apply typing.regular _ _ _ _ _ H₁
    | .inr Hvalue₀, .inl Hstep₁ =>
      have ⟨_, Hstep₁⟩ := Hstep₁
      apply step.congruence_under_ctx𝔹 _ _ _ _ (ctx𝔹.binaryr₁ _ _ _) Hstep₁
      apply Hvalue₀
    | .inr Hvalue₀, .inr Hvalue₁ =>
      cases Hvalue₀ <;> try contradiction
      case lit n₀ =>
      cases Hvalue₁ <;> try contradiction
      case lit n₁ =>
        exists .lit (eval op n₀ n₁)
        apply step_lvl.pure _ _ _ ctx𝕄.hole
        . constructor; simp; simp
        . apply head.binary₁
  case binary₂ op _ _ _ _ H₀ H₁ IH₀ IH₁ HDyn HEq𝕊 =>
    left
    match IH₀ HDyn HEq𝕊, IH₁ HDyn HEq𝕊 with
    | .inl Hstep₀, _ =>
      have ⟨_, Hstep₀⟩ := Hstep₀
      apply step.congruence_under_ctx𝔹 _ _ _ _ (ctx𝔹.binaryl₂ _ _ _) Hstep₀
      apply typing.regular _ _ _ _ _ H₁
    | .inr Hvalue₀, .inl Hstep₁ =>
      have ⟨_, Hstep₁⟩ := Hstep₁
      apply step.congruence_under_ctx𝔹 _ _ _ _ (ctx𝔹.binaryr₂ _ _ _) Hstep₁
      apply Hvalue₀
    | .inr Hvalue₀, .inr Hvalue₁ =>
      cases Hvalue₀ <;> try contradiction
      case code e₀ Hlc₀ =>
      cases Hvalue₁ <;> try contradiction
      case code e₁ Hlc₁ =>
        exists .reflect (.binary₁ op e₀ e₁)
        apply step_lvl.pure _ _ _ ctx𝕄.hole
        . constructor; apply Hlc₀; apply Hlc₁
        . apply head.binary₂
  case reflect e _ H _ _ _ =>
    left
    exists .lets𝕔 e (.code (.bvar 0))
    apply step_lvl.reflect _ _ _ ctxℙ.hole ctx𝔼.hole
    apply typing.regular _ _ _ _ _ H
  case lam𝕔 Γ e _ _ _ H Hwbt Hclosed IH HDyn HEq𝕊 =>
    left
    rw [← identity.closing_opening 0 _ _ Hclosed]
    match IH (dyn_env.extend _ _ HDyn) with
    | .inl Hstep =>
      have ⟨_, Hstep⟩ := Hstep
      constructor
      apply step.congruence_under_ctxℝ _ _ _ _ _ ctxℝ.lam𝕔 Hstep
    | .inr Hvalue =>
      generalize HEqe : ({0 ↦ Γ.length} e) = eₒ
      rw [HEqe] at Hvalue H
      cases Hvalue <;> try contradiction
      case code e Hlc =>
        exists .reflect (.lam ({0 ↤ Γ.length} e))
        apply step_lvl.pure _ _ _ ctx𝕄.hole
        . apply lc.under_closing; omega
          apply lc.inc; apply Hlc; omega
        . apply head.lam𝕔
  case lets e₀ e₁ _ _ _ _ H₀ H₁ _ _ IH₀ IH₁ HDyn HEq𝕊 =>
    left
    match IH₀ HDyn HEq𝕊 with
    | .inl Hstep₀ =>
      have ⟨_, Hstep₀⟩ := Hstep₀
      apply step.congruence_under_ctx𝔹 _ _ _ _ (ctx𝔹.lets _ _) Hstep₀
      rw [← lc.under_opening]; apply typing.regular _ _ _ _ _ H₁
    | .inr Hvalue₀ =>
      exists opening 0 e₀ e₁
      apply step_lvl.pure _ _ _ ctx𝕄.hole
      . constructor
        . apply lc.value _ Hvalue₀
        . rw [← lc.under_opening]; apply typing.regular _ _ _ _ _ H₁
      . apply head.lets; apply Hvalue₀
  case lets𝕔 Γ b e _ _ _ H₀ H₁ HwellBHwbtnds Hclosed _ IH₁ HDyn HEq𝕊 =>
    left
    rw [← identity.closing_opening 0 _ _ Hclosed]
    match IH₁ (dyn_env.extend _ _ HDyn) with
    | .inl Hstep₁ =>
      have ⟨_, Hstep₁⟩ := Hstep₁
      constructor
      apply step.congruence_under_ctxℝ _ _ _ _ _ (ctxℝ.lets𝕔 _ _) Hstep₁
      apply typing.regular _ _ _ _ _ H₀
    | .inr Hvalue₁ =>
      generalize HEqe : ({0 ↦ Γ.length} e) = eₒ
      rw [HEqe] at Hvalue₁ H₁
      cases Hvalue₁ <;> try contradiction
      case code e₁ Hlc₁ =>
        exists .code (.lets b ({0 ↤ Γ.length} e₁))
        apply step_lvl.pure _ _ _ ctx𝕄.hole
        . constructor
          . apply typing.regular _ _ _ _ _ H₀
          . apply lc.under_closing; omega
            apply lc.inc; apply Hlc₁; omega
        . apply head.lets𝕔
  case run H Hclosed IH HDyn HEq𝕊 =>
    left
    match IH HDyn with
    | .inl Hstep =>
      have ⟨_, Hstep⟩ := Hstep
      constructor
      apply step.congruence_under_ctxℝ _ _ _ _ _ ctxℝ.run Hstep
    | .inr Hvalue =>
      cases Hvalue <;> try contradiction
      case code e Hlc =>
        exists e
        apply step_lvl.pure _ _ _ ctx𝕄.hole
        . apply Hlc
        . apply head.run
  case fix₁ f _ _ _ _ _ _ _ IH HDyn HEq𝕊 =>
    left
    match IH HDyn HEq𝕊 with
    | .inl Hstep =>
      have ⟨_, Hstep⟩ := Hstep
      apply step.congruence_under_ctx𝔹 _ _ _ _ ctx𝔹.fix₁ Hstep
    | .inr Hvalue =>
      exists .lam (.app₁ (.app₁ f (.fix₁ f)) (.bvar 0))
      apply step_lvl.pure _ _ _ ctx𝕄.hole
      . apply lc.value _ Hvalue
      . apply head.fix₁; apply Hvalue
  case fix₂ H IH HDyn HEq𝕊 =>
    left
    match IH HDyn HEq𝕊 with
    | .inl Hstep =>
      have ⟨_, Hstep⟩ := Hstep
      apply step.congruence_under_ctx𝔹 _ _ _ _ ctx𝔹.fix₂ Hstep
    | .inr Hvalue =>
      cases Hvalue <;> try contradiction
      case code e Hlc =>
        exists .reflect (.fix₁ e)
        apply step_lvl.pure _ _ _ ctx𝕄.hole
        . apply Hlc
        . apply head.fix₂
  case ifz₁ l r _ _ _ _ H₀ H₁ H₂ IH₀ _ _ HDyn HEq𝕊 =>
    left
    match IH₀ HDyn HEq𝕊 with
    | .inl Hstep₀ =>
      have ⟨_, Hstep₀⟩ := Hstep₀
      apply step.congruence_under_ctx𝔹 _ _ _ _ (ctx𝔹.ifz₁ _ _ _ _) Hstep₀
      apply typing.regular _ _ _ _ _ H₁
      apply typing.regular _ _ _ _ _ H₂
    | .inr Hvalue =>
      cases Hvalue <;> try contradiction
      case lit c =>
      cases c
      case zero =>
        exists l
        apply step_lvl.pure _ _ _ ctx𝕄.hole
        . constructor; simp
          constructor; apply typing.regular _ _ _ _ _ H₁; apply typing.regular _ _ _ _ _ H₂
        . apply head.ifz₁_then
      case succ =>
        exists r
        apply step_lvl.pure _ _ _ ctx𝕄.hole
        . constructor; simp
          constructor; apply typing.regular _ _ _ _ _ H₁; apply typing.regular _ _ _ _ _ H₂
        . apply head.ifz₁_else
  case ifz₂ H₀ H₁ H₂ IH₀ IH₁ IH₂ HDyn HEq𝕊 =>
    left
    match IH₀ HDyn HEq𝕊, IH₁ HDyn, IH₂ HDyn with
    | .inl Hstep₀, _, _ =>
      have ⟨_, Hstep₀⟩ := Hstep₀
      apply step.congruence_under_ctx𝔹 _ _ _ _ (ctx𝔹.ifz₂ _ _ _ _) Hstep₀
      apply typing_reification.regular _ _ _ _ H₁
      apply typing_reification.regular _ _ _ _ H₂
    | .inr Hvalue₀, .inl Hstep₁, _ =>
      have ⟨_, Hstep₁⟩ := Hstep₁
      constructor
      apply step.congruence_under_ctxℝ _ _ _ _ _ (ctxℝ.ifzl₂ _ _ _ _) Hstep₁
      apply Hvalue₀
      apply typing_reification.regular _ _ _ _ H₂
    | .inr Hvalue₀, .inr Hvalue₁, .inl Hstep₂ =>
      have ⟨_, Hstep₂⟩ := Hstep₂
      constructor
      apply step.congruence_under_ctxℝ _ _ _ _ _ (ctxℝ.ifzr₂ _ _ _ _) Hstep₂
      apply Hvalue₀; apply Hvalue₁
    | .inr Hvalue₀, .inr Hvalue₁, .inr Hvalue₂ =>
      cases Hvalue₀ <;> try contradiction
      case code e₀ Hlc₀ =>
      cases Hvalue₁ <;> try contradiction
      case code e₁ Hlc₁ =>
      cases Hvalue₂ <;> try contradiction
      case code e₂ Hlc₂ =>
        exists .reflect (.ifz₁ e₀ e₁ e₂)
        apply step_lvl.pure _ _ _ ctx𝕄.hole
        . constructor; apply Hlc₀
          constructor; apply Hlc₁
          apply Hlc₂
        . apply head.ifz₂
  case pure IH HDyn => apply IH HDyn rfl
  case reify IH HDyn => apply IH HDyn rfl
  apply Hτ

theorem progress :
  ∀ e₀ τ φ,
    typing_reification ⦰ e₀ τ φ →
    (∃ e₁, (e₀ ⇝ e₁)) ∨ value e₀ :=
  by
  intros _ _ _ Hτ
  apply progress.strengthened ⦰ _ _ _ Hτ (by simp)
