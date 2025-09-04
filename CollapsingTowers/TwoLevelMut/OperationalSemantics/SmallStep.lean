import CollapsingTowers.TwoLevelMut.OperationalSemantics.EvalCtx
import CollapsingTowers.TwoLevelMut.OperationalSemantics.Store

inductive head_pure : Expr → Expr → Prop where
  | lets : ∀ e v, value v → head_pure (.lets v e) (opening 0 v e)
  | app₁ : ∀ e v, value v → head_pure (.app₁ (.lam e) v) (opening 0 v e)
  | app₂ : ∀ f arg, head_pure (.app₂ (.code f) (.code arg)) (.reflect (.app₁ f arg))
  | lift_lit : ∀ n, head_pure (.lift (.lit n)) (.reflect (.lit n))
  | lift_lam : ∀ e, head_pure (.lift (.lam e)) (.lam𝕔 (codify 0 e))
  | lam𝕔 : ∀ e, head_pure (.lam𝕔 (.code e)) (.reflect (.lam e))
  | lets𝕔 : ∀ b e, head_pure (.lets𝕔 b (.code e)) (.code (.lets b e))
  | run : ∀ e, head_pure (.run (.code e)) e
  | load₂ : ∀ e, head_pure (.load₂ (.code e)) (.reflect (.load₁ e))
  | alloc₂ : ∀ e, head_pure (.alloc₂ (.code e)) (.reflect (.alloc₁ e))
  | store₂ : ∀ l r, head_pure (.store₂ (.code l) (.code r)) (.reflect (.store₁ l r))

inductive head_mutable : (Store × Expr) → (Store × Expr) → Prop where
  | alloc₁ : ∀ σ n, head_mutable ⟨σ, .alloc₁ (.lit n)⟩ ⟨.lit n :: σ, .loc (σ.length)⟩
  | load₁ : ∀ σ l n, binds l (.lit n) σ → head_mutable ⟨σ, .load₁ (.loc l)⟩ ⟨σ, .lit n⟩
  | store₁ : ∀ σ₀ σ₁ l n, patch l (.lit n) σ₀ σ₁ → head_mutable ⟨σ₀, .store₁ (.loc l) (.lit n)⟩ ⟨σ₁, .unit⟩

inductive step_lvl (lvl : ℕ) : (Store × Expr) → (Store × Expr) → Prop where
  | pure : ∀ M e₀ e₁ σ, ctx𝕄 lvl M → lc e₀ → head_pure e₀ e₁ → step_lvl lvl ⟨σ, M⟦e₀⟧⟩ ⟨σ, M⟦e₁⟧⟩
  | mutable : ∀ M σ₀ σ₁ e₀ e₁, ctx𝕄 lvl M → lc e₀ → head_mutable ⟨σ₀, e₀⟩ ⟨σ₁, e₁⟩ → step_lvl lvl ⟨σ₀, M⟦e₀⟧⟩ ⟨σ₁, M⟦e₁⟧⟩
  | reflect : ∀ P E b σ, ctxℙ lvl P → ctx𝔼 E → lc b → step_lvl lvl ⟨σ, P⟦E⟦.reflect b⟧⟧⟩ ⟨σ, P⟦.lets𝕔 b E⟦.code (.bvar 0)⟧⟧⟩

notation:max st₀ " ⇝ " st₁  => step_lvl 0 st₀ st₁

inductive stepn : (Store × Expr) → (Store × Expr) → Prop
  | refl : ∀ st, stepn st st
  | multi : ∀ st₀ st₁ st₂, (st₀ ⇝ st₁) → stepn st₁ st₂ → stepn st₀ st₂

notation:max st₀ " ⇝* " st₁  => stepn st₀ st₁

lemma stepn.trans : ∀ st₀ st₁ st₂, (st₀ ⇝* st₁) → (st₁ ⇝* st₂) → (st₀ ⇝* st₂) :=
  by
  intros st₀ st₁ st₂ Hstep₀ Hstep₁
  induction Hstep₀
  case refl => apply Hstep₁
  case multi H _ IH =>
    apply stepn.multi
    apply H; apply IH; apply Hstep₁

lemma head_pure.fv_shrink : ∀ e₀ e₁, head_pure e₀ e₁ → fv e₁ ⊆ fv e₀ :=
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

lemma grounded.under_head_pure : ∀ e₀ e₁, head_pure e₀ e₁ → grounded e₀ → grounded e₁ :=
  by
  intros e₀ e₁ Hhead HG
  cases Hhead <;> simp at *
  case lets =>
    apply grounded.under_opening_value
    apply HG.left; apply HG.right
  case app₁ =>
    apply grounded.under_opening_value
    apply HG.right; apply HG.left

lemma grounded.under_head_mutable : ∀ σ₀ σ₁ e₀ e₁, head_mutable ⟨σ₀, e₀⟩ ⟨σ₁, e₁⟩ → grounded e₀ → grounded e₁ :=
  by
  intros σ₀ σ₁ e₀ e₁ Hmut HG
  cases Hmut <;> simp

lemma grounded.under_step : ∀ σ₀ σ₁ e₀ e₁, (⟨σ₀, e₀⟩ ⇝ ⟨σ₁, e₁⟩) → grounded e₀ → grounded e₁ :=
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
