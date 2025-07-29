import CollapsingTowers.TwoLevelBasic.Semantic.Deterministic

lemma value_ctx𝕄_impl_ctx_is_hole : ∀ lvl M e, ctx𝕄 lvl M → value M⟦e⟧ → M = id :=
  by
  intros lvl M e HM Hvalue
  cases HM
  case hole => rfl
  case cons𝔹 HB _ => exfalso; apply not_value.under_ctx𝔹; apply HB; apply Hvalue
  case consℝ HR _ => exfalso; apply not_value.under_ctxℝ; apply HR; apply Hvalue

lemma value_impl_termination : ∀ v e, value v → ¬(v ⇝ e) :=
  by
  intros v e Hvalue Hstep
  cases Hstep
  case pure HM _ Hhead =>
    rw [value_ctx𝕄_impl_ctx_is_hole _ _ _ HM Hvalue] at Hvalue
    cases Hhead <;> nomatch Hvalue
  case reflect P E _ HP HE _ =>
    have HM : ctx𝕄 0 (P ∘ E) :=
      by
      apply compose.ctx𝕄_ctx𝔼
      apply rewrite.ctxℙ_ctx𝕄
      apply HP; apply HE
    rw [ctx_comp P E, value_ctx𝕄_impl_ctx_is_hole _ _ _ HM Hvalue] at Hvalue
    nomatch Hvalue

theorem church_rosser :
  ∀ e l r,
    (e ⇝* l) →
    (e ⇝* r) →
    ∃ v,
      (l ⇝* v) ∧
      (r ⇝* v) :=
  by
  intros e l r Hstepl Hstepr
  induction Hstepl generalizing r
  case refl =>
    exists r; constructor
    . apply Hstepr
    . apply stepn.refl
  case multi le₀ le₁ le₂ IHstepl IHstepln IH =>
    cases Hstepr
    case refl =>
      exists le₂; constructor
      . apply stepn.refl
      . apply stepn.multi; apply IHstepl; apply IHstepln
    case multi re₀ IHstepr IHsteprn =>
      apply IH
      rw [deterministic _ _ _ IHstepl IHstepr]
      apply IHsteprn

theorem unique_normal_forms :
  ∀ e v₀ v₁,
    (e ⇝* v₀) →
    (e ⇝* v₁) →
    value v₀ →
    value v₁ →
    v₀ = v₁ :=
  by
  intros e v₀ v₁ Hstep₀ Hstep₁ Hvalue₀ Hvalue₁
  have ⟨v, Hstep₀, Hstep₁⟩ := church_rosser _ _ _ Hstep₀ Hstep₁
  cases Hstep₀
  case refl =>
    cases Hstep₁
    case refl => rfl
    case multi Hstep _ =>
      exfalso; apply value_impl_termination
      apply Hvalue₁; apply Hstep
  case multi Hstep _ =>
    exfalso; apply value_impl_termination
    apply Hvalue₀; apply Hstep
