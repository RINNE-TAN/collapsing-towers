import Instar.TwoLevelRec.OperationalSemantics.Deterministic

lemma value_ctx𝕄_impl_ctx_is_hole : ∀ lvl M e, ctx𝕄 lvl M → value M⟦e⟧ → M = id :=
  by
  intros lvl M e HM Hvalue
  cases HM
  case hole => rfl
  case cons𝔹 HB _ => exfalso; apply not_value.under_ctx𝔹; apply HB; apply Hvalue
  case consℝ HR _ => exfalso; apply not_value.under_ctxℝ; apply HR; apply Hvalue

lemma step.value_impl_termination : ∀ v e, value v → ¬(v ⭢ e) :=
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

lemma stepn.value_impl_termination : ∀ v₀ v₁, value v₀ → (v₀ ⭢* v₁) → v₀ = v₁ :=
  by
  intros v₀ v₁ Hvalue Hstepn
  cases Hstepn
  case refl => rfl
  case multi Hstep _ =>
    exfalso; apply step.value_impl_termination
    apply Hvalue; apply Hstep

lemma stepn_indexed.value_impl_termination : ∀ k v₀ v₁, value v₀ → (v₀ ⭢ ⟦k⟧ v₁) → v₀ = v₁ ∧ k = 0 :=
  by
  intros k v₀ v₁ Hvalue Hstepn
  cases Hstepn
  case refl => simp
  case multi Hstep _ =>
    exfalso; apply step.value_impl_termination
    apply Hvalue; apply Hstep

theorem stepn.church_rosser :
  ∀ e l r,
    (e ⭢* l) →
    (e ⭢* r) →
    ∃ v,
      (l ⭢* v) ∧
      (r ⭢* v) :=
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

theorem stepn_indexed.church_rosser :
  ∀ il ir e l r,
    (e ⭢ ⟦il⟧ l) →
    (e ⭢ ⟦ir⟧ r) →
    ∃ jl jr v,
      il + jl = ir + jr ∧
      (l ⭢ ⟦jl⟧ v) ∧
      (r ⭢ ⟦jr⟧ v) :=
  by
  intros il ir e l r Hstepl Hstepr
  induction Hstepl generalizing ir r
  case refl =>
    exists ir, 0, r
    constructor; omega
    constructor; apply Hstepr
    apply stepn_indexed.refl
  case multi il le₀ le₁ le₂ IHstepl IHstepln IH =>
    cases Hstepr
    case refl =>
      exists 0, il + 1, le₂
      constructor; omega
      constructor; apply stepn_indexed.refl
      apply stepn_indexed.multi
      apply IHstepl; apply IHstepln
    case multi ir re₀ IHstepr IHsteprn =>
      have IHstepln : (le₁ ⭢ ⟦ir⟧ r) :=
        by
        rw [deterministic _ _ _ IHstepl IHstepr]
        apply IHsteprn
      have ⟨jl, jr, v, IHEq, IHstep⟩ := IH _ _ IHstepln
      exists jl, jr, v
      constructor; omega
      apply IHstep

theorem stepn.unique_normal_forms :
  ∀ e v₀ v₁,
    (e ⭢* v₀) →
    (e ⭢* v₁) →
    value v₀ →
    value v₁ →
    v₀ = v₁ :=
  by
  intros e v₀ v₁ Hstep₀ Hstep₁ Hvalue₀ Hvalue₁
  have ⟨v, Hstep₀, Hstep₁⟩ := stepn.church_rosser _ _ _ Hstep₀ Hstep₁
  have HEq₀ := stepn.value_impl_termination _ _ Hvalue₀ Hstep₀
  have HEq₁ := stepn.value_impl_termination _ _ Hvalue₁ Hstep₁
  rw [HEq₀, HEq₁]

theorem stepn_indexed.unique_normal_forms :
  ∀ il ir e v₀ v₁,
    (e ⭢ ⟦il⟧ v₀) →
    (e ⭢ ⟦ir⟧ v₁) →
    value v₀ →
    value v₁ →
    v₀ = v₁ ∧ il = ir :=
  by
  intros il ir e v₀ v₁ Hstep₀ Hstep₁ Hvalue₀ Hvalue₁
  have ⟨z₀, z₁, r, HEq, Hstep₀, Hstep₁⟩ := stepn_indexed.church_rosser _ _ _ _ _ Hstep₀ Hstep₁
  have ⟨HEqv₀, HEqz₀⟩:= stepn_indexed.value_impl_termination _ _ _ Hvalue₀ Hstep₀
  have ⟨HEqv₁, HEqz₁⟩:= stepn_indexed.value_impl_termination _ _ _ Hvalue₁ Hstep₁
  simp [HEqv₀, HEqv₁]
  omega
