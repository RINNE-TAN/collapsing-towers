
import CollapsingTowers.TwoLevel.Typing
theorem progress_strengthened :
    ∀ Γ st₀ e₀ τ, typing_strengthened Γ e₀ τ -> value e₀ \/ ∃ st₁ e₁, step_lvl Γ.length (st₀, e₀) (st₁, e₁) :=
  by
  intros Γ st₀ e₀ τ H
  have ⟨HNeu, Hτ⟩ := H; clear H
  induction Hτ with
  | fvar => nomatch HNeu
  | lam₁ _ _ _ _ H =>
    left; constructor
    apply open_closedb; apply typing_regular; apply H
  | lam₂ _ _ _ _ H IH =>
    right
    cases IH HNeu with
    | inl Hvalue =>
      cases Hvalue with
      | lam₁ e Hlc =>
        exists st₀; exists .lam𝕔 (map𝕔₀ e)
        apply step_lvl.step𝕄 _ _ _ _ ctx𝕄.hole
        apply Hlc; apply head𝕄.lam₂
      | _ => nomatch H
    | inr Hstep =>
      have ⟨st₁, _, Hstep⟩ := Hstep; exists st₁
      apply step𝔹 _ _ _ _ _ _ ctx𝔹.lam₂; apply Hstep
  | app₁ _ e₀ e₁ _ _ H₀ H₁ IH₀ IH₁ =>
    right
    cases IH₀ HNeu.left with
    | inl Hvalue₀ =>
      cases IH₁ HNeu.right with
      | inl Hvalue₁ =>
        cases Hvalue₀ with
        | lam₁ e₀ Hlc₀ =>
          exists st₀; exists open_subst e₁ e₀
          apply step_lvl.step𝕄 _ _ _ _ ctx𝕄.hole
          constructor; apply Hlc₀; apply value_lc; apply Hvalue₁
          apply head𝕄.app₁; apply Hvalue₁
        | _ => nomatch H₀
      | inr Hstep₁ =>
        have ⟨st₁, _, Hstep₁⟩ := Hstep₁; exists st₁
        apply step𝔹 _ _ _ _ _ _ (ctx𝔹.appr₁ _ _); apply Hstep₁
        apply Hvalue₀
    | inr Hstep₀ =>
      have ⟨st₁, _, Hstep₀⟩ := Hstep₀; exists st₁
      apply step𝔹 _ _ _ _ _ _ (ctx𝔹.appl₁ _ _); apply Hstep₀
      apply typing_regular; apply H₁
  | app₂ _ e₀ e₁ _ _ H₀ H₁ IH₀ IH₁ =>
    right
    cases IH₀ HNeu.left with
    | inl Hvalue₀ =>
      cases IH₁ HNeu.right with
      | inl Hvalue₁ =>
        cases Hvalue₀ with
        | code e₀ Hlc₀ =>
          cases Hvalue₁ with
          | code e₁ Hlc₁ =>
            exists st₀; exists .reflect (.app₁ e₀ e₁)
            apply step_lvl.step𝕄 _ _ _ _ ctx𝕄.hole
            constructor; apply Hlc₀; apply Hlc₁
            apply head𝕄.app₂
          | _ => nomatch H₁
        | _ => nomatch H₀
      | inr Hstep₁ =>
        have ⟨st₁, _, Hstep₁⟩ := Hstep₁; exists st₁
        apply step𝔹 _ _ _ _ _ _ (ctx𝔹.appr₂ _ _); apply Hstep₁
        apply Hvalue₀
    | inr Hstep₀ =>
      have ⟨st₁, _, Hstep₀⟩ := Hstep₀; exists st₁
      apply step𝔹 _ _ _ _ _ _ (ctx𝔹.appl₂ _ _); apply Hstep₀
      apply typing_regular; apply H₁
  | plus₁ _ e₀ e₁ H₀ H₁ IH₀ IH₁ =>
    right
    cases IH₀ HNeu.left with
    | inl Hvalue₀ =>
      cases IH₁ HNeu.right with
      | inl Hvalue₁ =>
        cases Hvalue₀ with
        | lit₁ e₀ =>
          cases Hvalue₁ with
          | lit₁ e₁ =>
            exists st₀; exists .lit₁ (e₀ + e₁)
            apply step_lvl.step𝕄 _ _ _ _ ctx𝕄.hole
            simp; apply head𝕄.plus₁
          | _ => nomatch H₁
        | _ => nomatch H₀
      | inr Hstep₁ =>
        have ⟨st₁, _, Hstep₁⟩ := Hstep₁; exists st₁
        apply step𝔹 _ _ _ _ _ _ (ctx𝔹.plusr₁ _ _); apply Hstep₁
        apply Hvalue₀
    | inr Hstep₀ =>
      have ⟨st₁, _, Hstep₀⟩ := Hstep₀; exists st₁
      apply step𝔹 _ _ _ _ _ _ (ctx𝔹.plusl₁ _ _); apply Hstep₀
      apply typing_regular; apply H₁
  | plus₂ _ e₀ e₁ H₀ H₁ IH₀ IH₁ =>
    right
    cases IH₀ HNeu.left with
    | inl Hvalue₀ =>
      cases IH₁ HNeu.right with
      | inl Hvalue₁ =>
        cases Hvalue₀ with
        | code e₀ Hlc₀ =>
          cases Hvalue₁ with
          | code e₁ Hlc₁ =>
            exists st₀; exists .reflect (.plus₁ e₀ e₁)
            apply step_lvl.step𝕄 _ _ _ _ ctx𝕄.hole
            constructor; apply Hlc₀; apply Hlc₁
            apply head𝕄.plus₂
          | _ => nomatch H₁
        | _ => nomatch H₀
      | inr Hstep₁ =>
        have ⟨st₁, _, Hstep₁⟩ := Hstep₁; exists st₁
        apply step𝔹 _ _ _ _ _ _ (ctx𝔹.plusr₂ _ _); apply Hstep₁
        apply Hvalue₀
    | inr Hstep₀ =>
      have ⟨st₁, _, Hstep₀⟩ := Hstep₀; exists st₁
      apply step𝔹 _ _ _ _ _ _ (ctx𝔹.plusl₂ _ _); apply Hstep₀
      apply typing_regular; apply H₁
  | lit₁ => left; constructor
  | lit₂ _ _ H IH =>
    right
    cases IH HNeu with
    | inl Hvalue =>
      cases Hvalue with
      | lit₁ e =>
        exists st₀; exists .code (.lit₁ e)
        apply step_lvl.step𝕄 _ _ _ _ ctx𝕄.hole
        simp; apply head𝕄.lit₂
      | _ => nomatch H
    | inr Hstep =>
      have ⟨st₁, _, Hstep⟩ := Hstep; exists st₁
      apply step𝔹 _ _ _ _ _ _ ctx𝔹.lit₂; apply Hstep
  | code _ _ _ H =>
    left; constructor
    apply typing_regular; apply H
  | reflect _ e _ H =>
    right; exists st₀; constructor
    apply step_lvl.reflect _ _ _ _ ctxℙℚ.hole ctx𝔼.hole
    apply typing_regular; apply H
  | lam𝕔 Γ e _ _ H Hclose HNeulc IH =>
    right
    rw [← close_open_id₀ e _ Hclose]
    cases IH (neutral_inc _ _ _ HNeu HNeulc) with
    | inl Hvalue =>
      generalize HEqe : open₀ Γ.length e = e𝕠
      rw [HEqe] at Hvalue H
      cases Hvalue with
      | code e Hlc =>
        exists st₀; exists .reflect (.lam₁ (close₀ Γ.length e))
        apply step_lvl.step𝕄 _ _ _ _ ctx𝕄.hole
        apply close_closedb; omega
        apply closedb_inc; apply Hlc; omega
        apply head𝕄.lam𝕔
      | _ => nomatch H
    | inr Hstep =>
      have ⟨st₁, _, Hstep⟩ := Hstep; exists st₁
      constructor
      apply stepℝ _ _ _ _ _ _ ctxℝ.lam𝕔; apply Hstep
  | lets _ e₀ e₁ _ _ H₀ H₁ _ IH₀ IH₁ =>
    right
    cases IH₀ HNeu.left with
    | inl Hvalue₀ =>
      exists st₀; exists open_subst e₀ e₁
      apply step_lvl.step𝕄 _ _ _ _ ctx𝕄.hole
      constructor
      apply value_lc; apply Hvalue₀
      apply open_closedb; apply typing_regular; apply H₁
      apply head𝕄.lets; apply Hvalue₀
    | inr Hstep₀ =>
      have ⟨st₁, _, Hstep₀⟩ := Hstep₀; exists st₁
      apply step𝔹 _ _ _ _ _ _ (ctx𝔹.lets _ _); apply Hstep₀
      apply open_closedb; apply typing_regular; apply H₁
  | let𝕔 Γ b e _ _ H₀ H₁ Hclose HNeulc _ IH₁ =>
    right
    rw [← close_open_id₀ e _ Hclose]
    cases IH₁ (neutral_inc _ _ _ HNeu.right HNeulc) with
    | inl Hvalue =>
      generalize HEqe : open₀ Γ.length e = e𝕠
      rw [HEqe] at Hvalue H₁
      cases Hvalue with
      | code e Hlc =>
        exists st₀; exists .code (.lets b (close₀ Γ.length e))
        apply step_lvl.step𝕄 _ _ _ _ ctx𝕄.hole
        constructor
        apply typing_regular; apply H₀
        apply close_closedb; omega
        apply closedb_inc; apply Hlc; omega
        apply head𝕄.let𝕔₀
      | lit₁ e =>
        exists st₀; exists .lit₁ e
        apply step_lvl.step𝕄 _ _ _ _ ctx𝕄.hole
        constructor
        apply typing_regular; apply H₀
        simp
        apply head𝕄.let𝕔₁
      | lam₁ e Hlc =>
        exists st₀; exists .lam₁ (.let𝕔 b (swapdb 0 1 (closing 1 Γ.length e)))
        apply step_lvl.step𝕄 _ _ _ _ ctx𝕄.hole
        constructor
        apply typing_regular; apply H₀
        apply close_closedb; omega
        apply closedb_inc; apply Hlc; omega
        apply head𝕄.let𝕔₂
    | inr Hstep =>
      have ⟨st₁, _, Hstep⟩ := Hstep; exists st₁
      constructor
      apply stepℝ _ _ _ _ _ _ (ctxℝ.let𝕔 _ _); apply Hstep
      apply typing_regular; apply H₀

theorem progress : ∀ st₀ e₀ τ, typing [] e₀ τ -> value e₀ \/ ∃ st₁ e₁, step (st₀, e₀) (st₁, e₁) :=
  by
  intros _ _ _ Hτ
  rw [step, ← List.length_nil]
  apply progress_strengthened
  apply typing_weakening_empty
  apply Hτ
