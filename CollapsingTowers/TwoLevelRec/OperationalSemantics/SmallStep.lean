import CollapsingTowers.TwoLevelRec.OperationalSemantics.EvalCtx

inductive head : Expr → Expr → Prop where
  | lets : ∀ e v, value v → head (.lets v e) (opening 0 v e)
  | app₁ : ∀ e v, value v → head (.app₁ (.lam e) v) (opening 0 v e)
  | app₂ : ∀ f arg, head (.app₂ (.code f) (.code arg)) (.reflect (.app₁ f arg))
  | binary₁ : ∀ op l r, head (.binary₁ op (.lit l) (.lit r)) (.lit (eval op l r))
  | binary₂ : ∀ op l r, head (.binary₂ op (.code l) (.code r)) (.reflect (.binary₁ op l r))
  | lift_lit : ∀ n, head (.lift (.lit n)) (.reflect (.lit n))
  | lift_lam : ∀ e, head (.lift (.lam e)) (.lam𝕔 (codify 0 e))
  | lam𝕔 : ∀ e, head (.lam𝕔 (.code e)) (.reflect (.lam e))
  | lets𝕔 : ∀ b e, head (.lets𝕔 b (.code e)) (.code (.lets b e))
  | run : ∀ e, head (.run (.code e)) e
  -- fix f ↦ λx.f @ fix f @ x
  | fix₁ : ∀ f, value f → head (.fix₁ f) (.lam (.app₁ (.app₁ f (.fix₁ f)) (.bvar 0)))
  | fix₂ : ∀ f, head (.fix₂ (.code f)) (.reflect (.fix₁ f))
  | ifz₁_then : ∀ l r, head (.ifz₁ (.lit 0) l r) l
  | ifz₁_else : ∀ l r n, head (.ifz₁ (.lit (.succ n)) l r) r
  | ifz₂ : ∀ c l r, head (.ifz₂ (.code c) (.code l) (.code r)) (.reflect (.ifz₁ c l r))

inductive step_lvl (lvl : ℕ) : Expr → Expr → Prop where
  | pure : ∀ M e₀ e₁, ctx𝕄 lvl M → lc e₀ → head e₀ e₁ → step_lvl lvl M⟦e₀⟧ M⟦e₁⟧
  | reflect : ∀ P E b, ctxℙ lvl P → ctx𝔼 E → lc b → step_lvl lvl P⟦E⟦.reflect b⟧⟧ P⟦.lets𝕔 b E⟦.code (.bvar 0)⟧⟧

notation:max e₀ " ⇝ " e₁  => step_lvl 0 e₀ e₁

inductive stepn : Expr → Expr → Prop
  | refl : ∀ e, stepn e e
  | multi : ∀ e₀ e₁ e₂, (e₀ ⇝ e₁) → stepn e₁ e₂ → stepn e₀ e₂

notation:max e₀ " ⇝* " e₁  => stepn e₀ e₁

inductive stepn_indexed : ℕ → Expr → Expr → Prop
  | refl : ∀ e, stepn_indexed 0 e e
  | multi : ∀ k e₀ e₁ e₂, (e₀ ⇝ e₁) → stepn_indexed k e₁ e₂ → stepn_indexed (k + 1) e₀ e₂

notation:max e₀ " ⇝ " "⟦" k "⟧ " e₁  => stepn_indexed k e₀ e₁

lemma stepn.trans : ∀ e₀ e₁ e₂, (e₀ ⇝* e₁) → (e₁ ⇝* e₂) → (e₀ ⇝* e₂) :=
  by
  intros e₀ e₁ e₂ Hstep₀ Hstep₁
  induction Hstep₀
  case refl => apply Hstep₁
  case multi H _ IH =>
    apply stepn.multi
    apply H; apply IH; apply Hstep₁

lemma stepn_indexed.trans : ∀ i j e₀ e₁ e₂, (e₀ ⇝ ⟦i⟧ e₁) → (e₁ ⇝ ⟦j⟧ e₂) → (e₀ ⇝ ⟦i + j⟧ e₂) :=
  by
  intros i j e₀ e₁ e₂ Hstep₀ Hstep₁
  induction Hstep₀
  case refl => simp; apply Hstep₁
  case multi k _ _ _ H _ IH =>
    have HEq : k + 1 + j = k + j + 1 := by omega
    rw [HEq]
    apply stepn_indexed.multi
    apply H; apply IH; apply Hstep₁

lemma stepn_indexed_impl_stepn : ∀ k e₀ e₁, (e₀ ⇝ ⟦k⟧ e₁) → (e₀ ⇝* e₁) :=
  by
  intros k e₀ e₁ Hstepn
  induction Hstepn
  case refl => apply stepn.refl
  case multi H _ IH =>
    apply stepn.multi
    apply H; apply IH

lemma stepn_impl_stepn_indexed : ∀ e₀ e₁, (e₀ ⇝* e₁) → ∃ k, (e₀ ⇝ ⟦k⟧ e₁) :=
  by
  intros e₀ e₁ Hstepn
  induction Hstepn
  case refl => exists 0; apply stepn_indexed.refl
  case multi H _ IH =>
    have ⟨k, IH⟩ := IH
    exists k + 1
    apply stepn_indexed.multi
    apply H; apply IH

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
    simp [← fv.under_codify]

lemma lc.under_step : ∀ e₀ e₁, (e₀ ⇝ e₁) → lc e₀ :=
  by
  intros e₀ e₁ Hstep
  cases Hstep
  case pure HM Hlc Hhead =>
    apply lc.under_ctx𝕄; apply HM; apply Hlc
  case reflect HP HE Hlc =>
    apply lc.under_ctxℙ; apply HP
    apply lc.under_ctx𝔼; apply HE
    apply Hlc

lemma lc.under_stepn : ∀ e₀ e₁, (e₀ ⇝* e₁) → lc e₁ → lc e₀ :=
  by
  intros e₀ e₁ Hstepn Hlc
  induction Hstepn
  case refl => apply Hlc
  case multi H _ IH => apply lc.under_step; apply H

lemma lc.under_stepn_indexed : ∀ e₀ e₁ k, (e₀ ⇝ ⟦k⟧ e₁) → lc e₁ → lc e₀ :=
  by
  intros e₀ e₁ k Hstepn Hlc
  induction Hstepn
  case refl => apply Hlc
  case multi H _ IH => apply lc.under_step; apply H

lemma grounded.under_head : ∀ e₀ e₁, head e₀ e₁ → grounded e₀ → grounded e₁ :=
  by
  intros e₀ e₁ Hhead HG
  cases Hhead <;> simp at *
  case lets =>
    apply grounded.under_opening_value
    apply HG.left; apply HG.right
  case app₁ =>
    apply grounded.under_opening_value
    apply HG.right; apply HG.left
  case fix₁ => apply HG
  case ifz₁_then => apply HG.left
  case ifz₁_else => apply HG.right

lemma grounded.under_step : ∀ e₀ e₁, (e₀ ⇝ e₁) → grounded e₀ → grounded e₁ :=
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

lemma grounded.under_stepn : ∀ e₀ e₁, (e₀ ⇝* e₁) → grounded e₀ → grounded e₁ :=
  by
  intros e₀ e₁ Hstepn HG
  induction Hstepn
  case refl => apply HG
  case multi H _ IH =>
    apply IH; apply grounded.under_step
    apply H; apply HG
