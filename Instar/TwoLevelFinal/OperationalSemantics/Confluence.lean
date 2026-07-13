import Instar.TwoLevelFinal.OperationalSemantics.Deterministic

lemma value_ctx𝕄_impl_ctx_is_hole : ∀ lvl M e, ctx𝕄 lvl M → value M⟦e⟧ → M = id :=
  by
  intros lvl M e HM Hvalue
  cases HM
  case hole => rfl
  case cons𝔹 HB _ => exfalso; apply not_value.under_ctx𝔹; apply HB; apply Hvalue
  case consℝ HR _ => exfalso; apply not_value.under_ctxℝ; apply HR; apply Hvalue

lemma step.value_impl_termination : ∀ σ₀ σ₁ v e, value v → ¬(⟨σ₀, v⟩ ⭢ ⟨σ₁, e⟩) :=
  by
  intros σ₀ σ₁ v e Hvalue Hstep
  cases Hstep
  case pure  HM _ Hhead =>
    rw [value_ctx𝕄_impl_ctx_is_hole _ _ _ HM Hvalue] at Hvalue
    cases Hhead <;> nomatch Hvalue
  case mutable HM _ Hmut =>
    rw [value_ctx𝕄_impl_ctx_is_hole _ _ _ HM Hvalue] at Hvalue
    cases Hmut <;> nomatch Hvalue
  case reflect P E _ HP HE _ =>
    have HM : ctx𝕄 0 (P ∘ E) :=
      by
      apply compose.ctx𝕄_ctx𝔼
      apply rewrite.ctxℙ_ctx𝕄
      apply HP; apply HE
    rw [ctx_comp P E, value_ctx𝕄_impl_ctx_is_hole _ _ _ HM Hvalue] at Hvalue
    nomatch Hvalue

lemma stepn.value_impl_termination :
  ∀ σ₀ σ₁ v₀ v₁,
    value v₀ →
    (⟨σ₀, v₀⟩ ⭢* ⟨σ₁, v₁⟩) →
    σ₀ = σ₁ ∧ v₀ = v₁ :=
  by
  intros σ₀ σ₁ v₀ v₁ Hvalue Hstepn
  cases Hstepn
  case refl => simp
  case multi Hstep _ =>
    exfalso; apply step.value_impl_termination
    apply Hvalue; apply Hstep

lemma stepn_indexed.value_impl_termination :
  ∀ k σ₀ σ₁ v₀ v₁,
    value v₀ →
    (⟨σ₀, v₀⟩ ⭢ ⟦k⟧ ⟨σ₁, v₁⟩) →
    σ₀ = σ₁ ∧ v₀ = v₁ ∧ k = 0 :=
  by
  intros k σ₀ σ₁ v₀ v₁ Hvalue Hstepn
  cases Hstepn
  case refl => simp
  case multi Hstep _ =>
    exfalso; apply step.value_impl_termination
    apply Hvalue; apply Hstep

theorem stepn.church_rosser :
  ∀ st stl str,
    (st ⭢* stl) →
    (st ⭢* str) →
    ∃ stv,
      (stl ⭢* stv) ∧
      (str ⭢* stv) :=
  by
  intros st stl str Hstepl Hstepr
  induction Hstepl generalizing str
  case refl =>
    exists str; constructor
    . apply Hstepr
    . apply stepn.refl
  case multi stl₀ stl₁ stl₂ IHstepl IHstepln IH =>
    cases Hstepr
    case refl =>
      exists stl₂; constructor
      . apply stepn.refl
      . apply stepn.multi; apply IHstepl; apply IHstepln
    case multi str₀ IHstepr IHsteprn =>
      apply IH
      rcases stl₁ with ⟨σl₁, l₁⟩
      simp [deterministic _ _ _ _ _ _ IHstepl IHstepr]
      apply IHsteprn

theorem stepn_indexed.church_rosser :
  ∀ il ir st stl str,
    (st ⭢ ⟦il⟧ stl) →
    (st ⭢ ⟦ir⟧ str) →
    ∃ jl jr stv,
      il + jl = ir + jr ∧
      (stl ⭢ ⟦jl⟧ stv) ∧
      (str ⭢ ⟦jr⟧ stv) :=
  by
  intros il ir st stl str Hstepl Hstepr
  induction Hstepl generalizing ir str
  case refl =>
    exists ir, 0, str
    constructor; omega
    constructor; apply Hstepr
    apply stepn_indexed.refl
  case multi il stl₀ stl₁ stl₂ IHstepl IHstepln IH =>
    cases Hstepr
    case refl =>
      exists 0, il + 1, stl₂
      constructor; omega
      constructor; apply stepn_indexed.refl
      apply stepn_indexed.multi
      apply IHstepl; apply IHstepln
    case multi ir str₀ IHstepr IHsteprn =>
      rcases stl₁ with ⟨σl₁, l₁⟩
      have IHstepln : (⟨σl₁, l₁⟩ ⭢ ⟦ir⟧ str) :=
        by
        simp [deterministic _ _ _ _ _ _ IHstepl IHstepr]
        apply IHsteprn
      have ⟨jl, jr, v, IHEq, IHstep⟩ := IH _ _ IHstepln
      exists jl, jr, v
      constructor; omega
      apply IHstep

theorem stepn.unique_normal_forms :
  ∀ σ σ₀ σ₁ e v₀ v₁,
    (⟨σ, e⟩ ⭢* ⟨σ₀, v₀⟩) →
    (⟨σ, e⟩ ⭢* ⟨σ₁, v₁⟩) →
    value v₀ →
    value v₁ →
    σ₀ = σ₁ ∧ v₀ = v₁ :=
  by
  intros σ σ₀ σ₁ e v₀ v₁ Hstep₀ Hstep₁ Hvalue₀ Hvalue₁
  have ⟨stv, Hstep₀, Hstep₁⟩ := stepn.church_rosser _ _ _ Hstep₀ Hstep₁
  rcases stv with ⟨σ₂, v⟩
  have HEq₀ := stepn.value_impl_termination _ _ _ _ Hvalue₀ Hstep₀
  have HEq₁ := stepn.value_impl_termination _ _ _ _ Hvalue₁ Hstep₁
  simp [HEq₀, HEq₁]
