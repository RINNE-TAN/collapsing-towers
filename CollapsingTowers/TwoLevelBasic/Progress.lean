
import CollapsingTowers.TwoLevelBasic.Typing
@[simp]
def dyn_env (Γ : TEnv) : Prop :=
  ∀ x τ 𝕊, binds x (τ, 𝕊) Γ → ¬𝕊 = .stat

theorem dyn_env_extend :
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

theorem progress_strengthened :
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
  case fvar =>
    intros _ _ x _ Hbinds HwellBinds HDyn HEq𝕊
    exfalso; apply HDyn; apply Hbinds; apply HEq𝕊
  case lam =>
    intros _ _ _ _ _ _ H HwellBinds Hclose IH HDyn HEq𝕊
    left; constructor
    apply (open_lc _ _ _).mp; apply typing_regular; apply H
  case lift_lam =>
    intros _ _ _ _ _ _ H IH HDyn HEq𝕊
    right
    cases IH HDyn rfl with
    | inl Hvalue =>
      cases Hvalue with
      | lam e Hlc =>
        exists .lam𝕔 (map𝕔₀ e)
        apply step_lvl.step𝕄 _ _ _ ctx𝕄.hole
        apply Hlc; apply head𝕄.lift_lam
      | _ => nomatch H
    | inr Hstep =>
      have ⟨_, Hstep⟩ := Hstep
      apply step𝔹 _ _ _ _ ctx𝔹.lift; apply Hstep
  case app₁ =>
    intros _ _ e₀ e₁ _ _ _ _ _ H₀ H₁ IH₀ IH₁ HDyn HEq𝕊
    right
    cases IH₀ HDyn HEq𝕊 with
    | inl Hvalue₀ =>
      cases IH₁ HDyn HEq𝕊 with
      | inl Hvalue₁ =>
        cases Hvalue₀ with
        | lam e₀ Hlc₀ =>
          exists open_subst e₁ e₀
          apply step_lvl.step𝕄 _ _ _ ctx𝕄.hole
          constructor; apply Hlc₀; apply value_lc; apply Hvalue₁
          apply head𝕄.app₁; apply Hvalue₁
        | _ => nomatch H₀
      | inr Hstep₁ =>
        have ⟨_, Hstep₁⟩ := Hstep₁
        apply step𝔹 _ _ _ _ (ctx𝔹.appr₁ _ _); apply Hstep₁
        apply Hvalue₀
    | inr Hstep₀ =>
      have ⟨_, Hstep₀⟩ := Hstep₀
      apply step𝔹 _ _ _ _ (ctx𝔹.appl₁ _ _); apply Hstep₀
      apply typing_regular; apply H₁
  case app₂ =>
    intros _ e₀ e₁ _ _ _ _ H₀ H₁ IH₀ IH₁ HDyn HEq𝕊
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
            apply step_lvl.step𝕄 _ _ _ ctx𝕄.hole
            constructor; apply Hlc₀; apply Hlc₁
            apply head𝕄.app₂
          | _ => nomatch H₁
        | _ => nomatch H₀
      | inr Hstep₁ =>
        have ⟨_, Hstep₁⟩ := Hstep₁
        apply step𝔹 _ _ _ _ (ctx𝔹.appr₂ _ _); apply Hstep₁
        apply Hvalue₀
    | inr Hstep₀ =>
      have ⟨_, Hstep₀⟩ := Hstep₀
      apply step𝔹 _ _ _ _ (ctx𝔹.appl₂ _ _); apply Hstep₀
      apply typing_regular; apply H₁
  case lit => intros; left; constructor
  case lift_lit =>
    intros _ _ _ H IH HDyn HEq𝕊
    right
    cases IH HDyn HEq𝕊 with
    | inl Hvalue =>
      cases Hvalue with
      | lit e =>
        exists .reflect (.lit e)
        apply step_lvl.step𝕄 _ _ _ ctx𝕄.hole
        simp; apply head𝕄.lift_lit
      | _ => nomatch H
    | inr Hstep =>
      have ⟨_, Hstep⟩ := Hstep
      apply step𝔹 _ _ _ _ ctx𝔹.lift; apply Hstep
  case code_fragment => intros; left; constructor; simp
  case code_rep =>
    intros _ _ _ H IH HDyn HEq𝕊
    left; constructor
    apply typing_regular; apply H
  case reflect =>
    intros _ e _ H _ _ _
    right; exists .let𝕔 e (.code (.bvar 0))
    apply step_lvl.reflect _ _ _ ctxℙ.hole ctx𝔼.hole
    apply typing_regular; apply H
  case lam𝕔 =>
    intros Γ e _ _ _ H HwellBinds Hclose IH HDyn HEq𝕊
    right
    rw [← close_open_id₀ e _ Hclose]
    cases IH (dyn_env_extend _ _ HDyn) with
    | inl Hvalue =>
      generalize HEqe : open₀ Γ.length e = e𝕠
      rw [HEqe] at Hvalue H
      cases Hvalue with
      | code e Hlc =>
        exists .reflect (.lam (close₀ Γ.length e))
        apply step_lvl.step𝕄 _ _ _ ctx𝕄.hole
        apply close_lc; omega
        apply lc_inc; apply Hlc; omega
        apply head𝕄.lam𝕔
      | _ => contradiction
    | inr Hstep =>
      have ⟨_, Hstep⟩ := Hstep
      constructor
      apply stepℝ _ _ _ _ _ ctxℝ.lam𝕔; apply Hstep
  case lets =>
    intros _ _ e₀ e₁ _ _ _ _ H₀ H₁ _ _ IH₀ IH₁ HDyn HEq𝕊
    right
    cases IH₀ HDyn HEq𝕊 with
    | inl Hvalue₀ =>
      exists open_subst e₀ e₁
      apply step_lvl.step𝕄 _ _ _ ctx𝕄.hole
      constructor
      apply value_lc; apply Hvalue₀
      apply (open_lc _ _ _).mp; apply typing_regular; apply H₁
      apply head𝕄.lets; apply Hvalue₀
    | inr Hstep₀ =>
      have ⟨_, Hstep₀⟩ := Hstep₀
      apply step𝔹 _ _ _ _ (ctx𝔹.lets _ _); apply Hstep₀
      apply (open_lc _ _ _).mp; apply typing_regular; apply H₁
  case let𝕔 =>
    intros Γ b e _ _ _ H₀ H₁ HwellBinds Hclose _ IH₁ HDyn HEq𝕊
    right
    rw [← close_open_id₀ e _ Hclose]
    cases IH₁ (dyn_env_extend _ _ HDyn) with
    | inl Hvalue =>
      generalize HEqe : open₀ Γ.length e = e𝕠
      rw [HEqe] at Hvalue H₁
      cases Hvalue with
      | code e Hlc =>
        exists .code (.lets b (close₀ Γ.length e))
        apply step_lvl.step𝕄 _ _ _ ctx𝕄.hole
        constructor
        apply typing_regular; apply H₀
        apply close_lc; omega
        apply lc_inc; apply Hlc; omega
        apply head𝕄.let𝕔
      | _ => contradiction
    | inr Hstep =>
      have ⟨_, Hstep⟩ := Hstep
      constructor
      apply stepℝ _ _ _ _ _ (ctxℝ.let𝕔 _ _); apply Hstep
      apply typing_regular; apply H₀
  case run =>
    intros _ _ _ _ _ Hclose IH HDyn HEq𝕊
    right
    cases IH HDyn with
    | inl Hvalue =>
      cases Hvalue with
      | code e Hlc =>
        exists e
        apply step_lvl.step𝕄 _ _ _ ctx𝕄.hole
        apply Hlc
        apply head𝕄.run
      | _ => contradiction
    | inr Hstep =>
      have ⟨_, Hstep⟩ := Hstep
      constructor
      apply stepℝ _ _ _ _ _ ctxℝ.run; apply Hstep
  case pure =>
    intros _ _ _ _ IH HDyn
    apply IH; apply HDyn; rfl
  case reify =>
    intros _ _ _ _ _ IH HDyn
    apply IH; apply HDyn; rfl
  apply Hτ

theorem progress :
  ∀ e₀ τ φ,
    typing_reification [] e₀ τ φ →
    value e₀ ∨ ∃ e₁, step e₀ e₁ :=
  by
  intros _ _ _ Hτ
  rw [step, ← List.length_nil]
  apply progress_strengthened
  apply Hτ; simp
