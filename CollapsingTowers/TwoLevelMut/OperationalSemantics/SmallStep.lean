import CollapsingTowers.TwoLevelMut.OperationalSemantics.EvalCtx
import CollapsingTowers.TwoLevelMut.Utils.Defs

abbrev Store :=
  List Expr

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
  | store₂ : ∀ l r, head_pure (.app₂ (.code l) (.code r)) (.reflect (.store₁ l r))

inductive head_mutable : (Store × Expr) → (Store × Expr) → Prop where
  | alloc₁ : ∀ ω v, value v → head_mutable ⟨ω, .alloc₁ v⟩ ⟨v :: ω, .loc (ω.length)⟩
  | load₁ : ∀ ω l e, binds l e ω → head_mutable ⟨ω, .load₁ (.loc l)⟩ ⟨ω, e⟩
  | store₁ : ∀ ω₀ ω₁ l v, value v → patch l v ω₀ ω₁ → head_mutable ⟨ω₀, .store₁ (.loc l) v⟩ ⟨ω₁, .unit⟩

inductive step_lvl (lvl : ℕ) : (Store × Expr) → (Store × Expr) → Prop where
  | pure : ∀ M e₀ e₁ ω, ctx𝕄 lvl M → lc e₀ → head_pure e₀ e₁ → step_lvl lvl ⟨ω, M⟦e₀⟧⟩ ⟨ω, M⟦e₁⟧⟩
  | mutable : ∀ M ω₀ ω₁ e₀ e₁, ctx𝕄 lvl M → lc e₀ → head_mutable ⟨ω₀, e₀⟩ ⟨ω₁, e₁⟩ → step_lvl lvl ⟨ω₀, M⟦e₀⟧⟩ ⟨ω₁, M⟦e₁⟧⟩
  | reflect : ∀ P E b ω, ctxℙ lvl P → ctx𝔼 E → lc b → step_lvl lvl ⟨ω, P⟦E⟦.reflect b⟧⟧⟩ ⟨ω, P⟦.lets𝕔 b E⟦.code (.bvar 0)⟧⟧⟩

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
