
import Mathlib.Data.Finset.Basic
import CollapsingTowers.TwoLevel.Basic
import CollapsingTowers.TwoLevel.OpenClose
import CollapsingTowers.TwoLevel.Env
abbrev Ctx :=
  Expr -> Expr

notation:max a "⟦" b "⟧" => a b

inductive ctx𝔹 : Ctx -> Prop where
  | appl₁ : ∀ arg, ctx𝔹 (fun X => .app₁ X arg)
  | appr₁ : ∀ v, value v -> ctx𝔹 (fun X => .app₁ v X)
  | appl₂ : ∀ arg, ctx𝔹 (fun X => .app₂ X arg)
  | appr₂ : ∀ v, value v -> ctx𝔹 (fun X => .app₂ v X)
  | plusl₁ : ∀ r, ctx𝔹 (fun X => .plus₁ X r)
  | plusr₁ : ∀ v, value v -> ctx𝔹 (fun X => .plus₁ v X)
  | plusl₂ : ∀ r, ctx𝔹 (fun X => .plus₂ X r)
  | plusr₂ : ∀ v, value v -> ctx𝔹 (fun X => .plus₂ v X)
  | lets : ∀ e, ctx𝔹 (fun X => .lets X e)

inductive ctxℝ : ℕ -> Ctx -> Prop where
  | lam𝕔 : ctxℝ lvl (fun X => .lam𝕔 (close₀ lvl X))
  | let𝕔 : ∀ b, ctxℝ lvl (fun X => .let𝕔 b (close₀ lvl X))

inductive ctx𝕄 : ℕ -> Ctx -> Prop where
  | hole : ctx𝕄 lvl id
  | cons𝔹 : ∀ B M, ctx𝔹 B -> ctx𝕄 lvl M -> ctx𝕄 lvl (B ∘ M)
  | consℝ : ∀ R M, ctxℝ lvl R -> ctx𝕄 (lvl + 1) M -> ctx𝕄 lvl (R ∘ M)

inductive ctx𝔼 : Ctx -> Prop where
  | hole : ctx𝔼 (fun X => X)
  | cons𝔹 : ∀ B E, ctx𝔹 B -> ctx𝔼 E -> ctx𝔼 (B ∘ E)

mutual
  inductive ctxℙ : ℕ -> Ctx -> Prop where
    | hole : ctxℙ lvl (fun X => X)
    | cons𝔹 : ∀ B Q, ctx𝔹 B -> ctxℚ lvl Q -> ctxℙ lvl (B ∘ Q)
    | consℝ : ∀ R P, ctxℝ lvl R -> ctxℙ (lvl + 1) P -> ctxℙ lvl (R ∘ P)
  inductive ctxℚ : ℕ -> Ctx -> Prop where
    | cons𝔹 : ∀ B Q, ctx𝔹 B -> ctxℚ lvl Q -> ctxℚ lvl (B ∘ Q)
    | consℝ : ∀ R P, ctxℝ lvl R -> ctxℙ (lvl + 1) P -> ctxℚ lvl (R ∘ P)
end

inductive step : Expr -> Expr -> Prop where
  | lets : ∀ M e v, ctx𝕄 0 M -> value v -> step M⟦.lets v e⟧ M⟦open_subst v e⟧
  | app₁ : ∀ M e v, ctx𝕄 0 M -> value v -> step M⟦.app₁ (.lam₁ e) v⟧ M⟦open_subst v e⟧
  | app₂ : ∀ M f arg, ctx𝕄 0 M -> step M⟦.app₂ (.code f) (.code arg)⟧ M⟦.reflect (.app₁ f arg)⟧
  | plus₁ : ∀ M l r, ctx𝕄 0 M -> step M⟦.plus₁ (.lit₁ l) (.lit₁ r)⟧ M⟦.lit₁ (l + r)⟧
  | plus₂ : ∀ M l r, ctx𝕄 0 M -> step M⟦.plus₂ (.code l) (.code r)⟧ M⟦.reflect (.plus₁ l r)⟧
  | lit₂ : ∀ M n, ctx𝕄 0 M -> step M⟦.lit₂ n⟧ M⟦.code (.lit₁ n)⟧
  | lam₂ : ∀ M e, ctx𝕄 0 M -> step M⟦.lam₂ e⟧ M⟦.lam𝕔 (map𝕔₀ e)⟧
  | lam𝕔 : ∀ M e, ctx𝕄 0 M -> step M⟦.lam𝕔 (.code e)⟧ M⟦.reflect (.lam₁ e)⟧
  | reflect : ∀ P E b, ctxℙ 0 P -> ctx𝔼 E -> step P⟦E⟦.reflect b⟧⟧ P⟦.let𝕔 b E⟦.code (.bvar 0)⟧⟧
  | let𝕔 : ∀ M b e, ctx𝕄 0 M -> step M⟦.let𝕔 b (.code e)⟧ M⟦.code (.lets b e)⟧

inductive stepn : Expr → Expr → Prop
  | refl : ∀ e, stepn e e
  | multi : ∀ e₁ e₂ e₃, stepn e₁ e₂ → step e₂ e₃ → stepn e₁ e₃

/-- Examples:
lam₂ x. x +₂ (x +₂ x)
→⋆
code {
  lets f = lam₁ x.
    lets y = x + x in
    lets z = x + y in z
  in f
}
-/
def x₀ : Expr :=
  .fvar 0

def x₁ : Expr :=
  .fvar 1

def x₂ : Expr :=
  .fvar 2

def x₃ : Expr :=
  .fvar 3

def expr₀ : Expr :=
  .lam₂ (close₀ 0 (.plus₂ x₀ (.plus₂ x₀ x₀)))

def expr₁ : Expr :=
  .lam𝕔 (close₀ 0 (.plus₂ (.code x₀) (.plus₂ (.code x₀) (.code x₀))))

def expr₂ : Expr :=
  .lam𝕔 (close₀ 0 (.plus₂ (.code x₀) (.reflect (.plus₁ x₀ x₀))))

def expr₃ : Expr :=
  .lam𝕔 (close₀ 0 (.let𝕔 (.plus₁ x₀ x₀) (close₀ 1 (.plus₂ (.code x₀) (.code x₁)))))

def expr₄ : Expr :=
  .lam𝕔 (close₀ 0 (.let𝕔 (.plus₁ x₀ x₀) (close₀ 1 (.reflect (.plus₁ x₀ x₁)))))

def expr₅ : Expr :=
  .lam𝕔 (close₀ 0 (.let𝕔 (.plus₁ x₀ x₀) (close₀ 1 (.let𝕔 (.plus₁ x₀ x₁) (close₀ 2 (.code x₂))))))

def expr₆ : Expr :=
  .lam𝕔 (close₀ 0 (.let𝕔 (.plus₁ x₀ x₀) (close₀ 1 (.code (.lets (.plus₁ x₀ x₁) (close₀ 2 x₂))))))

def expr₇ : Expr :=
  .lam𝕔 (close₀ 0 (.code (.lets (.plus₁ x₀ x₀) (close₀ 1 (.lets (.plus₁ x₀ x₁) (close₀ 2 x₂))))))

def expr₈ : Expr :=
  .reflect (.lam₁ (close₀ 0 (.lets (.plus₁ x₀ x₀) (close₀ 1 (.lets (.plus₁ x₀ x₁) (close₀ 2 x₂))))))

def expr₉ : Expr :=
  .let𝕔 (.lam₁ (close₀ 0 (.lets (.plus₁ x₀ x₀) (close₀ 1 (.lets (.plus₁ x₀ x₁) (close₀ 2 x₂)))))) (close₀ 3 (.code x₃))

def expr𝕩 : Expr :=
  .code (.lets (.lam₁ (close₀ 0 (.lets (.plus₁ x₀ x₀) (close₀ 1 (.lets (.plus₁ x₀ x₁) (close₀ 2 x₂)))))) (close₀ 3 x₃))

example : step expr₀ expr₁ := by
  rw [expr₀]
  rw [expr₁]
  apply step.lam₂ _ _ ctx𝕄.hole

example : step expr₁ expr₂ := by
  rw [expr₁]
  rw [expr₂]
  apply step.plus₂ _ _ _ (ctx𝕄.consℝ _ _ ctxℝ.lam𝕔 (ctx𝕄.cons𝔹 _ _ (ctx𝔹.plusr₂ _ _) ctx𝕄.hole))
  repeat constructor

example : step expr₂ expr₃ := by
  rw [expr₂]
  rw [expr₃]
  apply step.reflect _ _ _ (ctxℙ.consℝ _ _ ctxℝ.lam𝕔 ctxℙ.hole) (ctx𝔼.cons𝔹 _ _ (ctx𝔹.plusr₂ _ _) ctx𝔼.hole)
  repeat constructor

example : step expr₃ expr₄ := by
  rw [expr₃]
  rw [expr₄]
  apply step.plus₂ _ _ _ (ctx𝕄.consℝ _ _ ctxℝ.lam𝕔 (ctx𝕄.consℝ _ _ (ctxℝ.let𝕔 _) ctx𝕄.hole))

example : step expr₄ expr₅ := by
  rw [expr₄]
  rw [expr₅]
  apply step.reflect _ _ _ (ctxℙ.consℝ _ _ ctxℝ.lam𝕔 (ctxℙ.consℝ _ _ (ctxℝ.let𝕔 _) ctxℙ.hole)) ctx𝔼.hole

example : step expr₅ expr₆ := by
  rw [expr₅]
  rw [expr₆]
  apply step.let𝕔 _ _ _ (ctx𝕄.consℝ _ _ ctxℝ.lam𝕔 (ctx𝕄.consℝ _ _ (ctxℝ.let𝕔 _) ctx𝕄.hole))

example : step expr₆ expr₇ := by
  rw [expr₆]
  rw [expr₇]
  apply step.let𝕔 _ _ _ (ctx𝕄.consℝ _ _ ctxℝ.lam𝕔 ctx𝕄.hole)

example : step expr₇ expr₈ := by
  rw [expr₇]
  rw [expr₈]
  rw [x₀]
  rw [x₁]
  rw [x₂]
  simp
  apply step.lam𝕔 _ _ ctx𝕄.hole

example : step expr₈ expr₉ := by
  rw [expr₈]
  rw [expr₉]
  apply step.reflect _ _ _ ctxℙ.hole ctx𝔼.hole

example : step expr₉ expr𝕩 := by
  rw [expr₉]
  rw [expr𝕩]
  apply step.let𝕔 _ _ _ ctx𝕄.hole
