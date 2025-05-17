
import CollapsingTowers.TwoLevel.Typing
theorem progress_strengthened : ∀ Γ e₀ τ, typing_strengthened Γ e₀ τ -> value e₀ \/ ∃ e₁, step_lvl Γ.length e₀ e₁ :=
  by
  intros Γ e₀ τ H
  have ⟨HNeu, Hτ⟩ := H; clear H
  induction Hτ with
  | fvar => nomatch HNeu
  | lam₁ _ _ _ _ Hτ =>
    left; constructor
    apply open_closedb; apply typing_regular; apply Hτ
  | lam₂ _ _ _ _ Hτ IH =>
    right
    cases IH HNeu with
    | inl Hvalue =>
      cases Hvalue with
      | lam₁ e Hlc =>
        exists .lam𝕔 (map𝕔₀ e)
        apply step_lvl.step𝕄 _ _ _ ctx𝕄.hole
        apply Hlc; apply head𝕄.lam₂
      | _ => nomatch Hτ
    | inr Hstep =>
      have ⟨_, Hstep⟩ := Hstep
      apply step𝔹 _ _ _ _ ctx𝔹.lam₂; apply Hstep
  | lam𝕔 Γ e _ _ Hτ Hclose HNeulc IH =>
    right
    rw [← close_open_id₀ e _ Hclose]
    cases IH (neutral_inc _ _ _ HNeu HNeulc) with
    | inl Hvalue =>
      generalize HEqe : open₀ Γ.length e = e𝕠
      rw [HEqe] at Hvalue Hτ
      cases Hvalue with
      | code e Hlc =>
        exists .reflect (.lam₁ (close₀ Γ.length e))
        apply step_lvl.step𝕄 _ _ _ ctx𝕄.hole
        apply close_closedb; omega
        apply closedb_inc; apply Hlc; omega
        constructor
      | _ => nomatch Hτ
    | inr Hstep =>
      have ⟨_, Hstep⟩ := Hstep
      constructor
      apply stepℝ _ _ _ _ ctxℝ.lam𝕔; apply Hstep
  | _ => admit

theorem progress : ∀ e₀ τ, typing [] e₀ τ -> value e₀ \/ ∃ e₁, step e₀ e₁ :=
  by
  intros _ _ Hτ
  rw [step, ← List.length_nil]
  apply progress_strengthened
  apply typing_weakening_empty
  apply Hτ
