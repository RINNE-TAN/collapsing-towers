import CollapsingTowers.TwoLevelRec.OperationalSemantics.Refine

-- e₁⇓ ≜ ∃ v, e ⇝* v
@[simp]
def termination (e : Expr) : Prop :=
  ∃ v, value v ∧ e ⇝* v

lemma termination.under_stepn :
  ∀ e₀ e₁,
    (e₀ ⇝* e₁) →
    (termination e₀ ↔ termination e₁) :=
  by
  intros e₀ e₁ Hstepl
  constructor
  . intro Htermination
    have ⟨v, Hvalue, Hstepr⟩ := Htermination
    exists v; constructor
    . apply Hvalue
    . have ⟨r, Hstepl, Hstepr⟩ := stepn.church_rosser _ _ _ Hstepl Hstepr
      have HEq := stepn.value_impl_termination _ _ Hvalue Hstepr
      rw [HEq]
      apply Hstepl
  . intro Htermination
    have ⟨v, Hvalue, Hstepr⟩ := Htermination
    exists v; constructor
    . apply Hvalue
    . apply stepn.trans _ _ _ Hstepl Hstepr

lemma termination.refl : ∀ z e, (e ⇝ ⟦z⟧ e) → termination e → z = 0 :=
  by
  intros zl₀ e Hstepl₀ Htermination
  have ⟨v, Hvalue, Hstepr₀⟩ := Htermination
  have ⟨zr₀, Hstepr₀⟩ := stepn_impl_stepn_indexed _ _ Hstepr₀
  have ⟨zl₁, zr₁, r, HEq, Hstepl₁, Hstepr₁⟩ := stepn_indexed.church_rosser _ _ _ _ _ Hstepl₀ Hstepr₀
  have ⟨HEqv, HEqzr₁⟩:= stepn_indexed.value_impl_termination _ _ _ Hvalue Hstepr₁
  rw [← HEqv] at Hstepl₁
  have ⟨_, HEqz⟩ := stepn_indexed.unique_normal_forms _ _ _ _ _ Hstepr₀ Hstepl₁ Hvalue Hvalue
  omega

-- λf.λx.f @ x
def F : Expr := .lam (.lam (.app₁ (.bvar 1) (.bvar 0)))

-- fix(F) @ 17
def diverge : Expr := .app₁ (.fix₁ F) (.lit 17)

theorem divergence : ¬termination diverge :=
  by
  intro Htermination
  have Htermination : termination (.app₁ (.lam (.app₁ (.app₁ F (.fix₁ F)) (.bvar 0))) (.lit 17)) :=
    by
    rw [← termination.under_stepn]
    apply Htermination
    simp [diverge, F]
    apply stepn.multi _ _ _ _ (stepn.refl _)
    apply step_lvl.pure (fun X => .app₁ X (.lit 17))
    apply ctx𝕄.cons𝔹 _ _ (ctx𝔹.appl₁ _ _)
    apply ctx𝕄.hole
    repeat constructor
  --
  --
  -- ⇝ F @ fix(F) @ 17
  have Hstep₀ : (
    (.app₁ (.lam (.app₁ (.app₁ F (.fix₁ F)) (.bvar 0))) (.lit 17)) ⇝
    (.app₁ (.app₁ F (.fix₁ F)) (.lit 17))
  ) :=
    by
    simp [F]
    apply step_lvl.pure id
    apply ctx𝕄.hole
    repeat constructor
  --
  --
  -- ⇝ F @ (λx.F @ fix(F) @ x) @ 17
  have Hstep₁ : (
    (.app₁ (.app₁ F (.fix₁ F)) (.lit 17)) ⇝
    (.app₁ (.app₁ F (.lam (.app₁ (.app₁ F (.fix₁ F)) (.bvar 0)))) (.lit 17))
  ) :=
    by
    simp [F]
    apply step_lvl.pure (fun X => .app₁ (.app₁ F X) (.lit 17))
    apply ctx𝕄.cons𝔹 _ _ (ctx𝔹.appl₁ _ _)
    apply ctx𝕄.cons𝔹 _ _ (ctx𝔹.appr₁ _ _)
    apply ctx𝕄.hole
    repeat constructor
  --
  --
  -- ⇝ (λx.(λy.F @ fix(F) @ y) @ x) @ 17
  have Hstep₂ : (
    (.app₁ (.app₁ F (.lam (.app₁ (.app₁ F (.fix₁ F)) (.bvar 0)))) (.lit 17)) ⇝
    (.app₁ (.lam (.app₁ (.lam (.app₁ (.app₁ F (.fix₁ F)) (.bvar 0))) (.bvar 0))) (.lit 17))
  ) :=
    by
    simp [F]
    apply step_lvl.pure (fun X => .app₁ X (.lit 17))
    apply ctx𝕄.cons𝔹 _ _ (ctx𝔹.appl₁ _ _)
    apply ctx𝕄.hole
    repeat constructor
  --
  --
  -- ⇝ (λx.F @ fix(F) @ x) @ 17
  have Hstep₃ : (
    (.app₁ (.lam (.app₁ (.lam (.app₁ (.app₁ F (.fix₁ F)) (.bvar 0))) (.bvar 0))) (.lit 17)) ⇝
    (.app₁ (.lam (.app₁ (.app₁ F (.fix₁ F)) (.bvar 0))) (.lit 17))
  ) :=
    by
    simp [F]
    apply step_lvl.pure id
    apply ctx𝕄.hole
    repeat constructor
  --
  --
  -- (λx.F @ fix(F) @ x) @ 17 ⇝ ⟦4⟧ (λx.F @ fix(F) @ x) @ 17
  have Hstepn : (
    (.app₁ (.lam (.app₁ (.app₁ F (.fix₁ F)) (.bvar 0))) (.lit 17)) ⇝ ⟦4⟧
    (.app₁ (.lam (.app₁ (.app₁ F (.fix₁ F)) (.bvar 0))) (.lit 17))
  ) :=
    by
    apply stepn_indexed.multi _ _ _ _ Hstep₀
    apply stepn_indexed.multi _ _ _ _ Hstep₁
    apply stepn_indexed.multi _ _ _ _ Hstep₂
    apply stepn_indexed.multi _ _ _ _ Hstep₃
    apply stepn_indexed.refl
  nomatch termination.refl _ _ Hstepn Htermination
