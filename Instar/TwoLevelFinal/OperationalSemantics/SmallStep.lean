import Instar.TwoLevelFinal.OperationalSemantics.EvalCtx
import Instar.TwoLevelFinal.OperationalSemantics.Store

inductive head_pure : Expr → Expr → Prop where
  | lets : ∀ e v, value v → head_pure (.lets v e) (opening 0 v e)
  | app₁ : ∀ e v, value v → head_pure (.app₁ (.lam e) v) (opening 0 v e)
  | app₂ : ∀ f arg, head_pure (.app₂ (.code f) (.code arg)) (.reflect (.app₁ f arg))
  | binary₁ : ∀ op l r, head_pure (.binary₁ op (.lit l) (.lit r)) (.lit (eval op l r))
  | binary₂ : ∀ op l r, head_pure (.binary₂ op (.code l) (.code r)) (.reflect (.binary₁ op l r))
  | lift_lit : ∀ n, head_pure (.lift (.lit n)) (.reflect (.lit n))
  | lift_lam : ∀ e, head_pure (.lift (.lam e)) (.lam𝕔 (codify 0 e))
  | lift_unit : head_pure (.lift .unit) (.reflect .unit)
  | lam𝕔 : ∀ e, head_pure (.lam𝕔 (.code e)) (.reflect (.lam e))
  | lets𝕔 : ∀ b e, head_pure (.lets𝕔 b (.code e)) (.code (.lets b e))
  | run : ∀ e, head_pure (.run (.code e)) e
  | load₂ : ∀ e, head_pure (.load₂ (.code e)) (.reflect (.load₁ e))
  | alloc₂ : ∀ e, head_pure (.alloc₂ (.code e)) (.reflect (.alloc₁ e))
  | store₂ : ∀ l r, head_pure (.store₂ (.code l) (.code r)) (.reflect (.store₁ l r))
  -- fix f ↦ λx.f @ fix f @ x
  | fix₁ : ∀ f, value f → head_pure (.fix₁ f) (.lam (.app₁ (.app₁ f (.fix₁ f)) (.bvar 0)))
  | fix₂ : ∀ f, head_pure (.fix₂ (.code f)) (.reflect (.fix₁ f))
  | ifz₁_then : ∀ l r, head_pure (.ifz₁ (.lit 0) l r) l
  | ifz₁_else : ∀ l r n, head_pure (.ifz₁ (.lit (.succ n)) l r) r
  | ifz₂ : ∀ c l r, head_pure (.ifz₂ (.code c) (.code l) (.code r)) (.reflect (.ifz₁ c l r))

notation e₀:39 " ↝ " e₁:39 => head_pure e₀ e₁

inductive head_mutable : (Store × Expr) → (Store × Expr) → Prop where
  | alloc₁ : ∀ σ n, head_mutable ⟨σ, .alloc₁ (.lit n)⟩ ⟨.lit n :: σ, .loc (σ.length)⟩
  | load₁ : ∀ σ l n, binds l (.lit n) σ → head_mutable ⟨σ, .load₁ (.loc l)⟩ ⟨σ, .lit n⟩
  | store₁ : ∀ σ₀ σ₁ l n, patch l (.lit n) σ₀ σ₁ → head_mutable ⟨σ₀, .store₁ (.loc l) (.lit n)⟩ ⟨σ₁, .unit⟩

inductive step_lvl (lvl : ℕ) : (Store × Expr) → (Store × Expr) → Prop where
  | pure : ∀ M e₀ e₁ σ, ctx𝕄 lvl M → lc e₀ → e₀ ↝ e₁ → step_lvl lvl ⟨σ, M⟦e₀⟧⟩ ⟨σ, M⟦e₁⟧⟩
  | mutable : ∀ M σ₀ σ₁ e₀ e₁, ctx𝕄 lvl M → lc e₀ → head_mutable ⟨σ₀, e₀⟩ ⟨σ₁, e₁⟩ → step_lvl lvl ⟨σ₀, M⟦e₀⟧⟩ ⟨σ₁, M⟦e₁⟧⟩
  | reflect : ∀ P E b σ, ctxℙ lvl P → ctx𝔼 E → lc b → step_lvl lvl ⟨σ, P⟦E⟦.reflect b⟧⟧⟩ ⟨σ, P⟦.lets𝕔 b E⟦.code (.bvar 0)⟧⟧⟩

notation st₀:39 " ⭢ " st₁:39  => step_lvl 0 st₀ st₁

inductive stepn : (Store × Expr) → (Store × Expr) → Prop
  | refl : ∀ st, stepn st st
  | multi : ∀ st₀ st₁ st₂, (st₀ ⭢ st₁) → stepn st₁ st₂ → stepn st₀ st₂

notation st₀:39 " ⭢* " st₁:39  => stepn st₀ st₁

inductive stepn_indexed : ℕ → (Store × Expr) → (Store × Expr) → Prop
  | refl : ∀ st, stepn_indexed 0 st st
  | multi : ∀ k st₀ st₁ st₂, (st₀ ⭢ st₁) → stepn_indexed k st₁ st₂ → stepn_indexed (k + 1) st₀ st₂

notation st₀:39 " ⭢ " "⟦" k "⟧ " st₁:39  => stepn_indexed k st₀ st₁

lemma stepn.trans : ∀ st₀ st₁ st₂, (st₀ ⭢* st₁) → (st₁ ⭢* st₂) → (st₀ ⭢* st₂) :=
  by
  intros st₀ st₁ st₂ Hstep₀ Hstep₁
  induction Hstep₀
  case refl => apply Hstep₁
  case multi H _ IH =>
    apply stepn.multi
    apply H; apply IH; apply Hstep₁

lemma stepn_indexed.trans : ∀ i j st₀ st₁ st₂, (st₀ ⭢ ⟦i⟧ st₁) → (st₁ ⭢ ⟦j⟧ st₂) → (st₀ ⭢ ⟦i + j⟧ st₂) :=
  by
  intros i j st₀ st₁ st₂ Hstep₀ Hstep₁
  induction Hstep₀
  case refl => simp; apply Hstep₁
  case multi k _ _ _ H _ IH =>
    have HEq : k + 1 + j = k + j + 1 := by omega
    rw [HEq]
    apply stepn_indexed.multi
    apply H; apply IH; apply Hstep₁

lemma stepn_indexed_impl_stepn : ∀ k st₀ st₁, (st₀ ⭢ ⟦k⟧ st₁) → (st₀ ⭢* st₁) :=
  by
  intros k st₀ st₁ Hstepn
  induction Hstepn
  case refl => apply stepn.refl
  case multi H _ IH =>
    apply stepn.multi
    apply H; apply IH

lemma stepn_impl_stepn_indexed : ∀ st₀ st₁, (st₀ ⭢* st₁) → ∃ k, (st₀ ⭢ ⟦k⟧ st₁) :=
  by
  intros st₀ st₁ Hstepn
  induction Hstepn
  case refl => exists 0; apply stepn_indexed.refl
  case multi H _ IH =>
    have ⟨k, IH⟩ := IH
    exists k + 1
    apply stepn_indexed.multi
    apply H; apply IH

lemma head_pure.fv_shrink : ∀ e₀ e₁, e₀ ↝ e₁ → fv e₁ ⊆ fv e₀ :=
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

lemma head_mutable.fv_shrink : ∀ σ₀ σ₁ e₀ e₁, head_mutable ⟨σ₀, e₀⟩ ⟨σ₁, e₁⟩ → fv e₁ ⊆ fv e₀ :=
  by
  intros σ₀ σ₁ e₀ e₁ Hmut
  cases Hmut <;> simp

lemma head_mutable.store_grow : ∀ σ₀ σ₁ e₀ e₁, head_mutable ⟨σ₀, e₀⟩ ⟨σ₁, e₁⟩ → σ₀.length ≤ σ₁.length :=
  by
  intros σ₀ σ₁ e₀ e₁ Hmut
  cases Hmut
  case alloc₁ => simp
  case load₁ => simp
  case store₁ Hpatch => simp [patch.length _ _ _ _ Hpatch]

lemma lc.under_step : ∀ σ₀ σ₁ e₀ e₁, (⟨σ₀, e₀⟩ ⭢ ⟨σ₁, e₁⟩) → lc e₀ :=
  by
  intros σ₀ σ₁ e₀ e₁ Hstep
  cases Hstep
  case pure HM Hlc Hhead =>
    apply lc.under_ctx𝕄; apply HM; apply Hlc
  case mutable HM Hlc Hhead =>
    apply lc.under_ctx𝕄; apply HM; apply Hlc
  case reflect HP HE Hlc =>
    apply lc.under_ctxℙ; apply HP
    apply lc.under_ctx𝔼; apply HE
    apply Hlc

lemma lc.under_stepn : ∀ σ₀ σ₁ e₀ e₁, (⟨σ₀, e₀⟩ ⭢* ⟨σ₁, e₁⟩) → lc e₁ → lc e₀ :=
  by
  intros σ₀ σ₂ e₀ e₂
  generalize HEq₀ : (σ₀, e₀) = st₀
  generalize HEq₁ : (σ₂, e₂) = st₂
  intros Hstepn Hlc
  induction Hstepn
  case refl =>
    simp [← HEq₀] at HEq₁
    rw [← HEq₁.right]
    apply Hlc
  case multi H _ IH =>
    apply lc.under_step
    simp [← HEq₀] at H
    apply H

lemma lc.under_stepn_indexed : ∀ k σ₀ σ₁ e₀ e₁, (⟨σ₀, e₀⟩ ⭢ ⟦k⟧ ⟨σ₁, e₁⟩) → lc e₁ → lc e₀ :=
  by
  intros k σ₀ σ₂ e₀ e₂
  generalize HEq₀ : (σ₀, e₀) = st₀
  generalize HEq₁ : (σ₂, e₂) = st₂
  intros Hstepn Hlc
  induction Hstepn
  case refl =>
    simp [← HEq₀] at HEq₁
    rw [← HEq₁.right]
    apply Hlc
  case multi H _ IH =>
    apply lc.under_step
    simp [← HEq₀] at H
    apply H

lemma grounded.under_head_pure : ∀ e₀ e₁, e₀ ↝ e₁ → grounded e₀ → grounded e₁ :=
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

lemma grounded.under_head_mutable : ∀ σ₀ σ₁ e₀ e₁, head_mutable ⟨σ₀, e₀⟩ ⟨σ₁, e₁⟩ → grounded e₀ → grounded e₁ :=
  by
  intros σ₀ σ₁ e₀ e₁ Hmut HG
  cases Hmut <;> simp

lemma grounded.under_step : ∀ σ₀ σ₁ e₀ e₁, (⟨σ₀, e₀⟩ ⭢ ⟨σ₁, e₁⟩) → grounded e₀ → grounded e₁ :=
  by
  intros σ₀ σ₁ e₀ e₁ Hstep HG
  cases Hstep
  case pure HM _ Hhead =>
    apply grounded.under_ctx𝕄; apply HM; apply HG
    apply grounded.under_head_pure; apply Hhead
    apply grounded.decompose_ctx𝕄; apply HM; apply HG
  case mutable HM _ Hmut =>
    apply grounded.under_ctx𝕄; apply HM; apply HG
    apply grounded.under_head_mutable; apply Hmut
    apply grounded.decompose_ctx𝕄; apply HM; apply HG
  case reflect M E _ HP HE _ =>
    have HM := rewrite.ctxℙ_ctx𝕄 _ _ HP
    have HG := grounded.decompose_ctx𝕄 _ _ _ HM HG
    have HG := grounded.decompose_ctx𝔼 _ _ HE HG
    simp at HG

lemma grounded.under_stepn : ∀ σ₀ σ₁ e₀ e₁, (⟨σ₀, e₀⟩ ⭢* ⟨σ₁, e₁⟩) → grounded e₀ → grounded e₁ :=
  by
  intros σ₀ σ₂ e₀ e₂
  generalize HEq₀ : (σ₀, e₀) = st₀
  generalize HEq₁ : (σ₂, e₂) = st₁
  intros Hstepn HG
  induction Hstepn generalizing σ₀ e₀
  case refl =>
    simp [← HEq₀] at HEq₁
    rw [HEq₁.right]
    apply HG
  case multi st₀ st₁ st₂ Hstep _ IH =>
    rcases st₁ with ⟨σ₁, e₁⟩
    apply IH _ _ rfl HEq₁
    apply grounded.under_step _ _ _ _ Hstep
    simp [← HEq₀]; apply HG

lemma store_free.under_head_pure : ∀ e₀ e₁, e₀ ↝ e₁ → store_free e₀ → store_free e₁ :=
  by
  intros e₀ e₁ Hhead
  cases Hhead <;> simp
  case lets =>
    apply store_free.under_opening_value
  case app₁ =>
    intros Hsf₀ Hsf₁
    apply store_free.under_opening_value _ _ _ Hsf₁ Hsf₀
  case lift_lam =>
    simp [← store_free.under_codify]
  case ifz₁_then =>
    intros Hsf₀ Hsf₁
    apply Hsf₀

lemma store_free.under_head_mutable : ∀ σ₀ σ₁ e₀ e₁, head_mutable ⟨σ₀, e₀⟩ ⟨σ₁, e₁⟩ → ¬store_free e₀ :=
  by
  intros σ₀ σ₁ e₀ e₁ Hmut Hsf
  cases Hmut <;> contradiction
