import CollapsingTowers.TwoLevelRec.OperationalSemantics.Refine

-- e₁⇓ ≜ ∃ v, e ⇝* v
@[simp]
def termination (e : Expr) : Prop :=
  ∃ v, value v ∧ e ⇝* v

-- λf.λx.f @ x
@[simp]
def fᵥ : Expr := .lam (.lam (.app₁ (.bvar 1) (.bvar 0)))

-- (λy.fᵥ @ fix(fᵥ) @ y) @ 17
@[simp]
def loop₀ : Expr := .app₁ (.lam (.app₁ (.app₁ fᵥ (.fix₁ fᵥ)) (.bvar 0))) (.lit 17)

-- fᵥ @ fix(fᵥ) @ 17
@[simp]
def loop₁ : Expr := .app₁ (.app₁ fᵥ (.fix₁ fᵥ)) (.lit 17)

-- fᵥ @ (λy.fᵥ @ fix(fᵥ) @ y) @ 17
@[simp]
def loop₂ : Expr := .app₁ (.app₁ fᵥ (.lam (.app₁ (.app₁ fᵥ (.fix₁ fᵥ)) (.bvar 0)))) (.lit 17)

-- (λx.(λy.fᵥ @ fix(fᵥ) @ y) @ x) @ 17
@[simp]
def loop₃ : Expr := .app₁ (.lam (.app₁ (.lam (.app₁ (.app₁ fᵥ (.fix₁ fᵥ)) (.bvar 0))) (.bvar 0))) (.lit 17)

@[simp]
def step₀ : (loop₀ ⇝ loop₁) :=
  by
  simp
  apply step_lvl.pure id
  apply ctx𝕄.hole
  repeat constructor

@[simp]
def step₁ : (loop₁ ⇝ loop₂) :=
  by
  simp
  apply step_lvl.pure (fun X => .app₁ (.app₁ fᵥ X) (.lit 17))
  apply ctx𝕄.cons𝔹 _ _ (ctx𝔹.appl₁ _ _)
  apply ctx𝕄.cons𝔹 _ _ (ctx𝔹.appr₁ _ _)
  apply ctx𝕄.hole
  repeat constructor

@[simp]
def step₂ : (loop₂ ⇝ loop₃) :=
  by
  simp
  apply step_lvl.pure (fun X => .app₁ X (.lit 17))
  apply ctx𝕄.cons𝔹 _ _ (ctx𝔹.appl₁ _ _)
  apply ctx𝕄.hole
  repeat constructor

@[simp]
def step₃ : (loop₃ ⇝ loop₀) :=
  by
  simp
  apply step_lvl.pure id
  apply ctx𝕄.hole
  repeat constructor

lemma termination.loop_impl_refl : ∀ z e, (e ⇝ ⟦z⟧ e) → termination e → z = 0 :=
  by
  intros zl₀ e Hstepl₀ Htermination
  have ⟨v, Hvalue, Hstepr₀⟩ := Htermination
  have ⟨zr₀, Hstepr₀⟩ := stepn_impl_stepn_indexed _ _ Hstepr₀
  have ⟨zl₁, zr₁, r, HEq, Hstepl₁, Hstepr₁⟩ := stepn_indexed.church_rosser _ _ _ _ _ Hstepl₀ Hstepr₀
  have ⟨HEqv, HEqzr₁⟩:= stepn_indexed.value_impl_termination _ _ _ Hvalue Hstepr₁
  rw [← HEqv] at Hstepl₁
  have ⟨_, HEqz⟩ := stepn_indexed.unique_normal_forms _ _ _ _ _ Hstepr₀ Hstepl₁ Hvalue Hvalue
  omega

theorem termination.loop : ¬termination loop₀ :=
  by
  intro Htermination
  have Hstep : (loop₀ ⇝ ⟦4⟧ loop₀) :=
    by
    apply stepn_indexed.multi _ _ _ _ step₀
    apply stepn_indexed.multi _ _ _ _ step₁
    apply stepn_indexed.multi _ _ _ _ step₂
    apply stepn_indexed.multi _ _ _ _ step₃
    apply stepn_indexed.refl
  have H := termination.loop_impl_refl _ _ Hstep Htermination
  omega
