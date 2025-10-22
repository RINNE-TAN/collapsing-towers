import CollapsingTowers.TwoLevelMut.SyntacticTyping.Defs
import CollapsingTowers.TwoLevelMut.OperationalSemantics.Defs

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
  ∀ σ₀ Γ e₀ τ φ ω,
    ok σ₀ →
    typing_reification σ₀ Γ e₀ τ φ ω →
    dyn_env Γ →
    (∃ σ₁ e₁, step_lvl Γ.length ⟨σ₀, e₀⟩ ⟨σ₁, e₁⟩) ∨ value e₀ :=
  by
  intros σ₀ Γ e₀ τ φ ω Hok Hτ
  apply @typing_reification.rec σ₀
    (fun Γ 𝕊 e₀ τ φ ω (H : typing σ₀ Γ 𝕊 e₀ τ φ ω) =>
      dyn_env Γ → 𝕊 = 𝟙 → (∃ σ₁ e₁, step_lvl Γ.length ⟨σ₀, e₀⟩ ⟨σ₁, e₁⟩) ∨ value e₀)
    (fun Γ e₀ τ φ ω (H : typing_reification σ₀ Γ e₀ τ φ ω) =>
      dyn_env Γ → (∃ σ₁ e₁, step_lvl Γ.length ⟨σ₀, e₀⟩ ⟨σ₁, e₁⟩) ∨ value e₀)
  <;> intros
  case fvar x _ Hbinds Hwbt HDyn HEq𝕊 => simp [HDyn _ _ _ Hbinds] at HEq𝕊
  case lam H Hwbt Hclosed IH HDyn HEq𝕊 => right; apply value.lam; simp; rw [← lc.under_opening]; apply typing.regular _ _ _ _ _ _ _ H
  case lit => right; apply value.lit
  case code_fragment => right; apply value.code; simp
  case code_rep H IH HDyn HEq𝕊 => right; apply value.code; apply typing.regular _ _ _ _ _ _ _ H
  case unit => right; apply value.unit
  case loc => right; apply value.loc
  case lift_lam H _ IH HDyn HEq𝕊 =>
    left
    match IH HDyn HEq𝕊 with
    | .inl Hstep =>
      have ⟨σ₁, _, Hstep⟩ := Hstep; exists σ₁
      apply step.congruence_under_ctx𝔹 _ _ _ _ _ _ ctx𝔹.lift Hstep
    | .inr Hvalue =>
      cases Hvalue <;> try contradiction
      case lam e Hlc =>
        exists σ₀, .lam𝕔 (codify 0 e)
        apply step_lvl.pure _ _ _ _ ctx𝕄.hole
        . apply Hlc
        . apply head_pure.lift_lam
  case app₁ e₀ e₁ _ _ _ _ _ _ _ _ H₀ H₁ IH₀ IH₁ HDyn HEq𝕊 =>
    left
    match IH₀ HDyn HEq𝕊, IH₁ HDyn HEq𝕊 with
    | .inl Hstep₀, _ =>
      have ⟨σ₁, _, Hstep₀⟩ := Hstep₀; exists σ₁
      apply step.congruence_under_ctx𝔹 _ _ _ _ _ _ (ctx𝔹.appl₁ _ _) Hstep₀
      apply typing.regular _ _ _ _ _ _ _ H₁
    | .inr Hvalue₀, .inl Hstep₁ =>
      have ⟨σ₁, _, Hstep₁⟩ := Hstep₁; exists σ₁
      apply step.congruence_under_ctx𝔹 _ _ _ _ _ _ (ctx𝔹.appr₁ _ _) Hstep₁
      apply Hvalue₀
    | .inr Hvalue₀, .inr Hvalue₁ =>
      cases Hvalue₀ <;> try contradiction
      case lam e₀ Hlc₀ =>
        exists σ₀, opening 0 e₁ e₀
        apply step_lvl.pure _ _ _ _ ctx𝕄.hole
        . constructor; apply Hlc₀; apply lc.value _ Hvalue₁
        . apply head_pure.app₁; apply Hvalue₁
  case app₂ e₀ e₁ _ _ _ _ _ _ H₀ H₁ IH₀ IH₁ HDyn HEq𝕊 =>
    left
    match IH₀ HDyn HEq𝕊, IH₁ HDyn HEq𝕊 with
    | .inl Hstep₀, _ =>
      have ⟨σ₁, _, Hstep₀⟩ := Hstep₀; exists σ₁
      apply step.congruence_under_ctx𝔹 _ _ _ _ _ _ (ctx𝔹.appl₂ _ _) Hstep₀
      apply typing.regular _ _ _ _ _ _ _ H₁
    | .inr Hvalue₀, .inl Hstep₁ =>
      have ⟨σ₁, _, Hstep₁⟩ := Hstep₁; exists σ₁
      apply step.congruence_under_ctx𝔹 _ _ _ _ _ _ (ctx𝔹.appr₂ _ _) Hstep₁
      apply Hvalue₀
    | .inr Hvalue₀, .inr Hvalue₁ =>
      cases Hvalue₀ <;> try contradiction
      case code e₀ Hlc₀ =>
      cases Hvalue₁ <;> try contradiction
      case code e₁ Hlc₁ =>
        exists σ₀, .reflect (.app₁ e₀ e₁)
        apply step_lvl.pure _ _ _ _ ctx𝕄.hole
        . constructor; apply Hlc₀; apply Hlc₁
        . apply head_pure.app₂
  case lift_lit H IH HDyn HEq𝕊 =>
    left
    match IH HDyn HEq𝕊 with
    | .inl Hstep =>
      have ⟨σ₁, _, Hstep⟩ := Hstep; exists σ₁
      apply step.congruence_under_ctx𝔹 _ _ _ _ _ _ ctx𝔹.lift Hstep
    | .inr Hvalue =>
      cases Hvalue <;> try contradiction
      case lit n =>
        exists σ₀, .reflect (.lit n)
        apply step_lvl.pure _ _ _ _ ctx𝕄.hole
        . simp
        . apply head_pure.lift_lit
  case lift_unit H IH HDyn HEq𝕊 =>
    left
    match IH HDyn HEq𝕊 with
    | .inl Hstep =>
      have ⟨σ₁, _, Hstep⟩ := Hstep; exists σ₁
      apply step.congruence_under_ctx𝔹 _ _ _ _ _ _ ctx𝔹.lift Hstep
    | .inr Hvalue =>
      cases Hvalue <;> try contradiction
      case unit =>
        exists σ₀, .reflect .unit
        apply step_lvl.pure _ _ _ _ ctx𝕄.hole
        . simp
        . apply head_pure.lift_unit
  case reflect e _ _ H _ _ _ =>
    left
    exists σ₀, .lets𝕔 e (.code (.bvar 0))
    apply step_lvl.reflect _ _ _ _ ctxℙ.hole ctx𝔼.hole
    apply typing.regular _ _ _ _ _ _ _ H
  case lam𝕔 Γ e _ _ _ _ H Hwbt Hclosed _ IH HDyn HEq𝕊 =>
    left
    rw [← identity.closing_opening 0 _ _ Hclosed]
    match IH (dyn_env.extend _ _ HDyn) with
    | .inl Hstep =>
      have ⟨σ₁, _, Hstep⟩ := Hstep; exists σ₁
      constructor
      apply step.congruence_under_ctxℝ _ _ _ _ _ _ _ ctxℝ.lam𝕔 Hstep
    | .inr Hvalue =>
      generalize HEqe : ({0 ↦ Γ.length} e) = eₒ
      rw [HEqe] at Hvalue H
      cases Hvalue <;> try contradiction
      case code e Hlc =>
        exists σ₀, .reflect (.lam ({0 ↤ Γ.length} e))
        apply step_lvl.pure _ _ _ _ ctx𝕄.hole
        . apply lc.under_closing; omega
          apply lc.inc; apply Hlc; omega
        . apply head_pure.lam𝕔
  case lets e₀ e₁ _ _ _ _ _ _ H₀ H₁ _ _ IH₀ IH₁ HDyn HEq𝕊 =>
    left
    match IH₀ HDyn HEq𝕊 with
    | .inl Hstep₀ =>
      have ⟨σ₁, _, Hstep₀⟩ := Hstep₀; exists σ₁
      apply step.congruence_under_ctx𝔹 _ _ _ _ _ _ (ctx𝔹.lets _ _) Hstep₀
      rw [← lc.under_opening]; apply typing.regular _ _ _ _ _ _ _ H₁
    | .inr Hvalue₀ =>
      exists σ₀, opening 0 e₀ e₁
      apply step_lvl.pure _ _ _ _ ctx𝕄.hole
      . constructor
        . apply lc.value _ Hvalue₀
        . rw [← lc.under_opening]; apply typing.regular _ _ _ _ _ _ _ H₁
      . apply head_pure.lets; apply Hvalue₀
  case lets𝕔 Γ b e _ _ _ _ _ H₀ H₁ HwellBHwbtnds Hclosed _ IH₁ HDyn HEq𝕊 =>
    left
    rw [← identity.closing_opening 0 _ _ Hclosed]
    match IH₁ (dyn_env.extend _ _ HDyn) with
    | .inl Hstep₁ =>
      have ⟨σ₁, _, Hstep₁⟩ := Hstep₁; exists σ₁
      constructor
      apply step.congruence_under_ctxℝ _ _ _ _ _ _ _ (ctxℝ.lets𝕔 _ _) Hstep₁
      apply typing.regular _ _ _ _ _ _ _ H₀
    | .inr Hvalue₁ =>
      generalize HEqe : ({0 ↦ Γ.length} e) = eₒ
      rw [HEqe] at Hvalue₁ H₁
      cases Hvalue₁ <;> try contradiction
      case code e₁ Hlc₁ =>
        exists σ₀, .code (.lets b ({0 ↤ Γ.length} e₁))
        apply step_lvl.pure _ _ _ _ ctx𝕄.hole
        . constructor
          . apply typing.regular _ _ _ _ _ _ _ H₀
          . apply lc.under_closing; omega
            apply lc.inc; apply Hlc₁; omega
        . apply head_pure.lets𝕔
  case run H Hclosed IH HDyn HEq𝕊 =>
    left
    match IH HDyn with
    | .inl Hstep =>
      have ⟨σ₁, _, Hstep⟩ := Hstep; exists σ₁
      constructor
      apply step.congruence_under_ctxℝ _ _ _ _ _ _ _ ctxℝ.run Hstep
    | .inr Hvalue =>
      cases Hvalue <;> try contradiction
      case code e Hlc =>
        exists σ₀, e
        apply step_lvl.pure _ _ _ _ ctx𝕄.hole
        . apply Hlc
        . apply head_pure.run
  case alloc₁ H IH HDyn HEq𝕊 =>
    left
    match IH HDyn HEq𝕊 with
    | .inl Hstep =>
      have ⟨σ₁, _, Hstep⟩ := Hstep; exists σ₁
      apply step.congruence_under_ctx𝔹 _ _ _ _ _ _ ctx𝔹.alloc₁ Hstep
    | .inr Hvalue =>
      cases Hvalue <;> try contradiction
      case lit n =>
        exists .lit n :: σ₀, .loc (σ₀.length)
        apply step_lvl.mutable _ _ _ _ _ ctx𝕄.hole
        . apply typing.regular _ _ _ _ _ _ _ H
        . apply head_mutable.alloc₁
  case alloc₂ H IH HDyn HEq𝕊 =>
    left
    match IH HDyn HEq𝕊 with
    | .inl Hstep =>
      have ⟨σ₁, _, Hstep⟩ := Hstep; exists σ₁
      apply step.congruence_under_ctx𝔹 _ _ _ _ _ _ ctx𝔹.alloc₂ Hstep
    | .inr Hvalue =>
      cases Hvalue <;> try contradiction
      case code e Hlc =>
        exists σ₀, .reflect (.alloc₁ e)
        apply step_lvl.pure _ _ _ _ ctx𝕄.hole
        . apply Hlc
        . apply head_pure.alloc₂
  case load₁ H IH HDyn HEq𝕊 =>
    left
    match IH HDyn HEq𝕊 with
    | .inl Hstep =>
      have ⟨σ₁, _, Hstep⟩ := Hstep; exists σ₁
      apply step.congruence_under_ctx𝔹 _ _ _ _ _ _ ctx𝔹.load₁ Hstep
    | .inr Hvalue =>
      cases Hvalue <;> try contradiction
      case loc l =>
      cases H
      case loc Hloc =>
        have ⟨v, Hbinds⟩ := (getr_exists_iff_index_lt_length _ _).mp Hloc
        have ⟨n, HEq⟩ := ok.binds _ _ _ Hok Hbinds
        rw [← HEq] at Hbinds
        exists σ₀, .lit n
        apply step_lvl.mutable _ _ _ _ _ ctx𝕄.hole
        . simp
        . apply head_mutable.load₁; apply Hbinds
  case load₂ H IH HDyn HEq𝕊 =>
    left
    match IH HDyn HEq𝕊 with
    | .inl Hstep =>
      have ⟨σ₁, _, Hstep⟩ := Hstep; exists σ₁
      apply step.congruence_under_ctx𝔹 _ _ _ _ _ _ ctx𝔹.load₂ Hstep
    | .inr Hvalue =>
      cases Hvalue <;> try contradiction
      case code e Hlc =>
        exists σ₀, .reflect (.load₁ e)
        apply step_lvl.pure _ _ _ _ ctx𝕄.hole
        . apply Hlc
        . apply head_pure.load₂
  case store₁ H₀ H₁ IH₀ IH₁ HDyn HEq𝕊 =>
    left
    match IH₀ HDyn HEq𝕊, IH₁ HDyn HEq𝕊 with
    | .inl Hstep₀, _ =>
      have ⟨σ₁, _, Hstep₀⟩ := Hstep₀; exists σ₁
      apply step.congruence_under_ctx𝔹 _ _ _ _ _ _ (ctx𝔹.storel₁ _ _) Hstep₀
      apply typing.regular _ _ _ _ _ _ _ H₁
    | .inr Hvalue₀, .inl Hstep₁ =>
      have ⟨σ₁, _, Hstep₁⟩ := Hstep₁; exists σ₁
      apply step.congruence_under_ctx𝔹 _ _ _ _ _ _ (ctx𝔹.storer₁ _ _) Hstep₁
      apply Hvalue₀
    | .inr Hvalue₀, .inr Hvalue₁ =>
      cases Hvalue₀ <;> try contradiction
      case loc l =>
      cases Hvalue₁ <;> try contradiction
      case lit n =>
      cases H₀
      case loc Hloc =>
        have ⟨σ₁, Hpatch⟩ := (setr_exists_iff_index_lt_length _ _ (.lit n)).mp Hloc
        exists σ₁, .unit
        apply step_lvl.mutable _ _ _ _ _ ctx𝕄.hole
        . simp
        . apply head_mutable.store₁; apply Hpatch
  case store₂ H₀ H₁ IH₀ IH₁ HDyn HEq𝕊 =>
    left
    match IH₀ HDyn HEq𝕊, IH₁ HDyn HEq𝕊 with
    | .inl Hstep₀, _ =>
      have ⟨σ₁, _, Hstep₀⟩ := Hstep₀; exists σ₁
      apply step.congruence_under_ctx𝔹 _ _ _ _ _ _ (ctx𝔹.storel₂ _ _) Hstep₀
      apply typing.regular _ _ _ _ _ _ _ H₁
    | .inr Hvalue₀, .inl Hstep₁ =>
      have ⟨σ₁, _, Hstep₁⟩ := Hstep₁; exists σ₁
      apply step.congruence_under_ctx𝔹 _ _ _ _ _ _ (ctx𝔹.storer₂ _ _) Hstep₁
      apply Hvalue₀
    | .inr Hvalue₀, .inr Hvalue₁ =>
      cases Hvalue₀ <;> try contradiction
      case code e₀ Hlc₀ =>
      cases Hvalue₁ <;> try contradiction
      case code e₁ Hlc₁ =>
        exists σ₀, .reflect (.store₁ e₀ e₁)
        apply step_lvl.pure _ _ _ _ ctx𝕄.hole
        . constructor; apply Hlc₀; apply Hlc₁
        . apply head_pure.store₂
  case pure IH HDyn => apply IH HDyn rfl
  case reify IH HDyn => apply IH HDyn rfl
  apply Hτ

theorem progress :
  ∀ σ₀ e₀ τ φ ω,
    ok σ₀ →
    typing_reification σ₀ ⦰ e₀ τ φ ω →
    (∃ σ₁ e₁, (⟨σ₀, e₀⟩ ⇝ ⟨σ₁, e₁⟩)) ∨ value e₀ :=
  by
  intros _ _ _ _ _ Hok Hτ
  apply progress.strengthened _ ⦰ _ _ _ _ Hok Hτ (by simp)
