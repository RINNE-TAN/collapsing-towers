import CollapsingTowers.TwoLevelRec.Semantic.Deterministic

lemma value_ctx𝕄_impl_ctx_is_hole : ∀ lvl M e, ctx𝕄 lvl M → value M⟦e⟧ → M = id :=
  by
  intros lvl M e HM Hvalue
  cases HM
  case hole => rfl
  case cons𝔹 HB _ => exfalso; apply not_value.under_ctx𝔹; apply HB; apply Hvalue
  case consℝ HR _ => exfalso; apply not_value.under_ctxℝ; apply HR; apply Hvalue

lemma step.value_impl_termination : ∀ v e, value v → ¬(v ⇝ e) :=
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

lemma stepn.value_impl_termination : ∀ v₀ v₁, value v₀ → (v₀ ⇝* v₁) → v₀ = v₁ :=
  by
  intros v₀ v₁ Hvalue Hstepn
  cases Hstepn
  case refl => rfl
  case multi Hstep _ =>
    exfalso; apply step.value_impl_termination
    apply Hvalue; apply Hstep

lemma pure_stepn_indexed.value_impl_termination : ∀ k v₀ v₁, value v₀ → (v₀ ⇾ ⟦k⟧ v₁) → v₀ = v₁ ∧ k = 0 :=
  by
  intros k v₀ v₁ Hvalue Hstepn
  cases Hstepn
  case refl => simp
  case multi Hstep _ =>
    exfalso; apply step.value_impl_termination
    apply Hvalue; apply pure_step_impl_step; apply Hstep

-- B⟦e⟧ ⇾ r
-- —————————————————————————————————
-- B⟦e₀⟧ ⇾ B⟦e₁⟧ ∧ e₀ ⇾ e₁
lemma pure_stepn_indexed.refine.under_ctx𝔹 :
  ∀ B e₀ r,
    ctx𝔹 B →
    (B⟦e₀⟧ ⇾ r) →
    ∃ e₁,
      (B⟦e₀⟧ ⇾ B⟦e₁⟧) ∧
      (e₀ ⇾ e₁) :=
  by
  intros B e₀ r HB
  generalize HEqe : B⟦e₀⟧ = E₀
  intros Hstep
  admit

-- B⟦e⟧ ⇾ₖ v
-- —————————————————————————————————
-- k = i + j ∧ e ⇾ᵢ v𝕖 ∧ B⟦v𝕖⟧ ⇾ⱼ v
lemma pure_stepn_indexed.refine :
  ∀ B e v k,
    ctx𝔹 B →
    value v →
    (B⟦e⟧ ⇾ ⟦k⟧ v) →
    ∃ v𝕖 i j,
      i + j = k ∧
      value v𝕖 ∧
      (e ⇾ ⟦i⟧ v𝕖) ∧
      (B⟦v𝕖⟧ ⇾ ⟦j⟧ v) :=
  by
  intros B e v k HB
  generalize HEqe : B⟦e⟧ = E
  intros Hvalue Hstep
  induction Hstep generalizing e
  case refl =>
    exfalso; apply not_value.under_ctx𝔹
    apply HB; rw [HEqe]; apply Hvalue
  case multi k e₀ e₁ e₂ Hstep _ IH =>
    admit

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
  have HEq₀ := stepn.value_impl_termination _ _ Hvalue₀ Hstep₀
  have HEq₁ := stepn.value_impl_termination _ _ Hvalue₁ Hstep₁
  rw [HEq₀, HEq₁]
