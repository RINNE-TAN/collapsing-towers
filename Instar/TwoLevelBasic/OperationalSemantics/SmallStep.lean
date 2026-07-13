import Instar.TwoLevelBasic.OperationalSemantics.EvalCtx

inductive head : Expr → Expr → Prop where
  | lets : ∀ e v, value v → head (.lets v e) (opening 0 v e)
  | app₁ : ∀ e v, value v → head (.app₁ (.lam e) v) (opening 0 v e)
  | app₂ : ∀ f arg, head (.app₂ (.code f) (.code arg)) (.reflect (.app₁ f arg))
  | lift_lit : ∀ n, head (.lift (.lit n)) (.reflect (.lit n))
  | lift_lam : ∀ e, head (.lift (.lam e)) (.lam𝕔 (codify 0 e))
  | lam𝕔 : ∀ e, head (.lam𝕔 (.code e)) (.reflect (.lam e))
  | lets𝕔 : ∀ b e, head (.lets𝕔 b (.code e)) (.code (.lets b e))
  | run : ∀ e, head (.run (.code e)) e

notation e₀:39 " ↝ " e₁:39 => head e₀ e₁

inductive step_lvl (lvl : ℕ) : Expr → Expr → Prop where
  | pure : ∀ M e₀ e₁, ctx𝕄 lvl M → lc e₀ → e₀ ↝ e₁ → step_lvl lvl M⟦e₀⟧ M⟦e₁⟧
  | reflect : ∀ P E b, ctxℙ lvl P → ctx𝔼 E → lc b → step_lvl lvl P⟦E⟦.reflect b⟧⟧ P⟦.lets𝕔 b E⟦.code (.bvar 0)⟧⟧

notation e₀:39 " ⭢ " e₁:39 => step_lvl 0 e₀ e₁

inductive stepn : Expr → Expr → Prop
  | refl : ∀ e, stepn e e
  | multi : ∀ e₀ e₁ e₂, e₀ ⭢ e₁ → stepn e₁ e₂ → stepn e₀ e₂

notation e₀:39 " ⭢* " e₁:39  => stepn e₀ e₁

lemma stepn.trans : ∀ e₀ e₁ e₂, (e₀ ⭢* e₁) → (e₁ ⭢* e₂) → (e₀ ⭢* e₂) :=
  by
  intros e₀ e₁ e₂ Hstep₀ Hstep₁
  induction Hstep₀
  case refl => apply Hstep₁
  case multi H _ IH =>
    apply stepn.multi
    apply H; apply IH; apply Hstep₁

lemma head.fv_shrink : ∀ e₀ e₁, e₀ ↝ e₁ → fv e₁ ⊆ fv e₀ :=
  by
  intros e₀ e₁ Hhead
  cases Hhead <;> simp
  case lets =>
    apply fv.under_opening
  case app₁ =>
    rw [Set.union_comm]
    apply fv.under_opening
  case lift_lam =>
    simp [← fv.under_codify]

lemma lc.under_step : ∀ e₀ e₁, (e₀ ⭢ e₁) → lc e₀ :=
  by
  intros e₀ e₁ Hstep
  cases Hstep
  case pure HM Hlc Hhead =>
    apply lc.under_ctx𝕄; apply HM; apply Hlc
  case reflect HP HE Hlc =>
    apply lc.under_ctxℙ; apply HP
    apply lc.under_ctx𝔼; apply HE
    apply Hlc

lemma lc.under_stepn : ∀ e₀ e₁, (e₀ ⭢* e₁) → lc e₁ → lc e₀ :=
  by
  intros e₀ e₁ Hstepn Hlc
  induction Hstepn
  case refl => apply Hlc
  case multi H _ IH => apply lc.under_step; apply H

lemma grounded.under_head : ∀ e₀ e₁, e₀ ↝ e₁ → grounded e₀ → grounded e₁ :=
  by
  intros e₀ e₁ Hhead HG
  cases Hhead <;> simp at *
  case lets =>
    apply grounded.under_opening_value
    apply HG.left; apply HG.right
  case app₁ =>
    apply grounded.under_opening_value
    apply HG.right; apply HG.left

lemma grounded.under_step : ∀ e₀ e₁, (e₀ ⭢ e₁) → grounded e₀ → grounded e₁ :=
  by
  intros e₀ e₁ Hstep HG
  cases Hstep
  case pure HM _ Hhead =>
    apply grounded.under_ctx𝕄; apply HM; apply HG
    apply grounded.under_head; apply Hhead
    apply grounded.decompose_ctx𝕄; apply HM; apply HG
  case reflect M E _ HP HE _ =>
    have HM := rewrite.ctxℙ_ctx𝕄 _ _ HP
    have HG := grounded.decompose_ctx𝕄 _ _ _ HM HG
    have HG := grounded.decompose_ctx𝔼 _ _ HE HG
    simp at HG

lemma grounded.under_stepn : ∀ e₀ e₁, (e₀ ⭢* e₁) → grounded e₀ → grounded e₁ :=
  by
  intros e₀ e₁ Hstepn HG
  induction Hstepn
  case refl => apply HG
  case multi H _ IH =>
    apply IH; apply grounded.under_step
    apply H; apply HG
