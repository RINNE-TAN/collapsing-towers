import CollapsingTowers.TwoLvLBasic.Semantic.EvalCtx

inductive head : Expr → Expr → Prop where
  | lets : ∀ e v, value v → head (.lets v e) ({0 ↦ v} e)
  | app₁ : ∀ e v, value v → head (.app₁ (.lam e) v) ({0 ↦ v} e)
  | app₂ : ∀ f arg, head (.app₂ (.code f) (.code arg)) (.reflect (.app₁ f arg))
  | lift_lit : ∀ n, head (.lift (.lit n)) (.reflect (.lit n))
  | lift_lam : ∀ e, head (.lift (.lam e)) (.lam𝕔 ({0 ↦ $0} e))
  | lam𝕔 : ∀ e, head (.lam𝕔 (.code e)) (.reflect (.lam e))
  | let𝕔 : ∀ b e, head (.lets𝕔 b (.code e)) (.code (.lets b e))
  | run : ∀ e, head (.run (.code e)) e

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

notation:max e₀ " ↦ " e₁  => pure_step e₀ e₁

inductive pure_stepn : Expr → Expr → Prop
  | refl : ∀ e, pure_stepn e e
  | multi : ∀ e₀ e₁ e₂, (e₀ ↦ e₁) → pure_stepn e₁ e₂ → pure_stepn e₀ e₂

notation:max e₀ " ↦* " e₁  => pure_stepn e₀ e₁

lemma pure_step_impl_step : ∀ e₀ e₁, (e₀ ↦ e₁) → (e₀ ⇝ e₁) :=
  by
  intros e₀ e₁ Hstep
  cases Hstep
  case pure HM Hlc Hhead =>
    apply step_lvl.pure
    apply HM; apply Hlc; apply Hhead

lemma pure_stepn_impl_stepn : ∀ e₀ e₁, (e₀ ↦* e₁) → (e₀ ⇝* e₁) :=
  by
  intros e₀ e₁ Hstepn
  induction Hstepn
  case refl => apply stepn.refl
  case multi H _ IH =>
    apply stepn.multi
    apply pure_step_impl_step; apply H
    apply IH

lemma pure_stepn.trans : ∀ e₀ e₁ e₂, (e₀ ↦* e₁) → (e₁ ↦* e₂) → (e₀ ↦* e₂) :=
  by
  intros e₀ e₁ e₂ Hstep₀ Hstep₁
  induction Hstep₀
  case refl => apply Hstep₁
  case multi H _ IH =>
    apply pure_stepn.multi
    apply H; apply IH; apply Hstep₁
