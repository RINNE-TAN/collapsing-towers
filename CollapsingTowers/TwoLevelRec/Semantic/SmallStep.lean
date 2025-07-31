import CollapsingTowers.TwoLevelRec.Semantic.EvalCtx

inductive head : Expr → Expr → Prop where
  | lets : ∀ e v, value v → head (.lets v e) (opening 0 v e)
  -- fix f x.e @ v ⇝ ⟦f ↦ fix f x.e⟧⟦x ↦ v⟧ e
  | app₁ : ∀ e v, value v → head (.app₁ (.fix e) v) (opening 1 v (opening 0 (.fix e) e))
  | app₂ : ∀ f arg, head (.app₂ (.code f) (.code arg)) (.reflect (.app₁ f arg))
  | lift_lit : ∀ n, head (.lift (.lit n)) (.reflect (.lit n))
  -- lift (fix f x.e) ⇝ fix𝕔 (⟦f ↦ code f⟧⟦x ↦ code x⟧ e)
  | lift_fix : ∀ e, head (.lift (.fix e)) (.fix𝕔 (maping𝕔 1 (maping𝕔 0 e)))
  | fix𝕔 : ∀ e, head (.fix𝕔 (.code e)) (.reflect (.fix e))
  | lets𝕔 : ∀ b e, head (.lets𝕔 b (.code e)) (.code (.lets b e))
  | run : ∀ e, head (.run (.code e)) e

inductive step_lvl (lvl : ℕ) : Expr → Expr → Prop where
  | pure : ∀ M e₀ e₁, ctx𝕄 lvl M → lc e₀ → head e₀ e₁ → step_lvl lvl M⟦e₀⟧ M⟦e₁⟧
  | reflect : ∀ P E b, ctxℙ lvl P → ctx𝔼 E → lc b → step_lvl lvl P⟦E⟦.reflect b⟧⟧ P⟦.lets𝕔 b E⟦.code (.bvar 0)⟧⟧

notation:max e₀ " ⇝ " e₁  => step_lvl 0 e₀ e₁

inductive stepn : Expr → Expr → Prop
  | refl : ∀ e, stepn e e
  | multi : ∀ e₀ e₁ e₂, (e₀ ⇝ e₁) → stepn e₁ e₂ → stepn e₀ e₂

notation:max e₀ " ⇝* " e₁  => stepn e₀ e₁
