import CollapsingTowers.TwoLevelRec.Semantic.EvalCtx

inductive head : Expr → Expr → Prop where
  | lets : ∀ e v, value v → head (.lets v e) (opening 0 v e)
  | app₁ : ∀ e v, value v → head (.app₁ (.lam e) v) (opening 0 v e)
  | app₂ : ∀ f arg, head (.app₂ (.code f) (.code arg)) (.reflect (.app₁ f arg))
  | lift_lit : ∀ n, head (.lift (.lit n)) (.reflect (.lit n))
  | lift_lam : ∀ e, head (.lift (.lam e)) (.lam𝕔 (maping𝕔 0 e))
  | lam𝕔 : ∀ e, head (.lam𝕔 (.code e)) (.reflect (.lam e))
  | lets𝕔 : ∀ b e, head (.lets𝕔 b (.code e)) (.code (.lets b e))
  | run : ∀ e, head (.run (.code e)) e
  -- fix F ↦ λx.F(fix F)(x)
  | fix₁ : ∀ f, value f → head (.fix₁ f) (.lam (.app₁ (.app₁ f (.fix₁ f)) (.bvar 0)))
  | fix₂ : ∀ f, head (.fix₂ (.code f)) (.reflect (.fix₁ f))

inductive step_lvl (lvl : ℕ) : Expr → Expr → Prop where
  | pure : ∀ M e₀ e₁, ctx𝕄 lvl M → lc e₀ → head e₀ e₁ → step_lvl lvl M⟦e₀⟧ M⟦e₁⟧
  | reflect : ∀ P E b, ctxℙ lvl P → ctx𝔼 E → lc b → step_lvl lvl P⟦E⟦.reflect b⟧⟧ P⟦.lets𝕔 b E⟦.code (.bvar 0)⟧⟧

notation:max e₀ " ⇝ " e₁  => step_lvl 0 e₀ e₁

inductive stepn : Expr → Expr → Prop
  | refl : ∀ e, stepn e e
  | multi : ∀ e₀ e₁ e₂, (e₀ ⇝ e₁) → stepn e₁ e₂ → stepn e₀ e₂

notation:max e₀ " ⇝* " e₁  => stepn e₀ e₁

inductive pure_step : Expr → Expr → Prop where
  | pure : ∀ M e₀ e₁, ctx𝕄 0 M → lc e₀ → head e₀ e₁ → pure_step M⟦e₀⟧ M⟦e₁⟧

notation:max e₀ " ⇾ " e₁  => pure_step e₀ e₁

inductive pure_stepn : Expr → Expr → Prop
  | refl : ∀ e, pure_stepn e e
  | multi : ∀ e₀ e₁ e₂, (e₀ ⇾ e₁) → pure_stepn e₁ e₂ → pure_stepn e₀ e₂

notation:max e₀ " ⇾* " e₁  => pure_stepn e₀ e₁

inductive pure_stepn_indexed : ℕ → Expr → Expr → Prop
  | refl : ∀ e, pure_stepn_indexed 0 e e
  | multi : ∀ k e₀ e₁ e₂, (e₀ ⇾ e₁) → pure_stepn_indexed k e₁ e₂ → pure_stepn_indexed (k + 1) e₀ e₂

notation:max e₀ " ⇾ " "⟦" k "⟧ " e₁  => pure_stepn_indexed k e₀ e₁

lemma pure_step_impl_step : ∀ e₀ e₁, (e₀ ⇾ e₁) → (e₀ ⇝ e₁) :=
  by
  intros e₀ e₁ Hstep
  cases Hstep
  case pure HM Hlc Hhead =>
    apply step_lvl.pure
    apply HM; apply Hlc; apply Hhead

lemma pure_stepn_impl_stepn : ∀ e₀ e₁, (e₀ ⇾* e₁) → (e₀ ⇝* e₁) :=
  by
  intros e₀ e₁ Hstepn
  induction Hstepn
  case refl => apply stepn.refl
  case multi H _ IH =>
    apply stepn.multi
    apply pure_step_impl_step; apply H
    apply IH

lemma pure_stepn_impl_pure_stepn_indexed : ∀ e₀ e₁, (e₀ ⇾* e₁) → ∃ k, (e₀ ⇾ ⟦k⟧ e₁) :=
  by
  intros e₀ e₁ Hstepn
  induction Hstepn
  case refl => exists 0; apply pure_stepn_indexed.refl
  case multi H _ IH =>
    have ⟨k, IH⟩ := IH
    exists k + 1
    apply pure_stepn_indexed.multi
    apply H; apply IH

lemma pure_stepn.trans : ∀ e₀ e₁ e₂, (e₀ ⇾* e₁) → (e₁ ⇾* e₂) → (e₀ ⇾* e₂) :=
  by
  intros e₀ e₁ e₂ Hstep₀ Hstep₁
  induction Hstep₀
  case refl => apply Hstep₁
  case multi H _ IH =>
    apply pure_stepn.multi
    apply H; apply IH; apply Hstep₁

lemma head.fv_shrink : ∀ e₀ e₁, head e₀ e₁ → fv e₁ ⊆ fv e₀ :=
  by
  intros e₀ e₁ Hhead
  cases Hhead <;> simp
  case lets =>
    apply fv.under_opening
  case app₁ =>
    rw [Set.union_comm]
    apply fv.under_opening
  case lift_lam =>
    rw [← fv.under_maping𝕔]

lemma lc.under_pure_step : ∀ e₀ e₁, (e₀ ⇾ e₁) → lc e₀ :=
  by
  intros e₀ e₁ Hstep
  cases Hstep
  case pure HM Hlc Hhead =>
    apply lc.under_ctx𝕄; apply HM; apply Hlc

lemma lc.under_pure_stepn : ∀ e₀ e₁, (e₀ ⇾* e₁) → lc e₁ → lc e₀ :=
  by
  intros e₀ e₁ Hstepn Hlc
  induction Hstepn
  case refl => apply Hlc
  case multi H _ IH => apply lc.under_pure_step; apply H

lemma lc.under_pure_stepn_indexed : ∀ e₀ e₁ k, (e₀ ⇾ ⟦k⟧ e₁) → lc e₁ → lc e₀ :=
  by
  intros e₀ e₁ k Hstepn Hlc
  induction Hstepn
  case refl => apply Hlc
  case multi H _ IH => apply lc.under_pure_step; apply H
