
import Mathlib.Data.Finset.Basic
import CollapsingTowers.TwoLevel.Basic
import CollapsingTowers.TwoLevel.OpenClose
import CollapsingTowers.TwoLevel.Env

abbrev Ctx := Expr -> Expr

notation:max a "⟦" b "⟧" => a b

inductive ctx𝔹 : Ctx -> Prop where
  | appl₁ : ∀ arg, lc arg -> ctx𝔹 (fun X => .app₁ X arg)
  | appr₁ : ∀ v, value v -> ctx𝔹 (fun X => .app₁ v X)
  | appl₂ : ∀ arg, lc arg -> ctx𝔹 (fun X => .app₂ X arg)
  | appr₂ : ∀ v, value v -> ctx𝔹 (fun X => .app₂ v X)
  | plusl₁ : ∀ r, lc r -> ctx𝔹 (fun X => .plus₁ X r)
  | plusr₁ : ∀ v, value v -> ctx𝔹 (fun X => .plus₁ v X)
  | plusl₂ : ∀ r, lc r -> ctx𝔹 (fun X => .plus₂ X r)
  | plusr₂ : ∀ v, value v -> ctx𝔹 (fun X => .plus₂ v X)
  | lets : ∀ e x, lc (open₀ x e) -> ctx𝔹 (fun X => .lets X e)

inductive ctxℝ : Ctx -> Prop where
  | lam𝕔 : ∀ x, ctxℝ (fun X => .lam𝕔 (close₀ x X))
  | let𝕔 : ∀ b x, lc b -> ctxℝ (fun X => .let𝕔 b (close₀ x X))

inductive ctx𝕄 : Ctx -> Prop where
  | hole : ctx𝕄 id
  | cons𝔹 : ∀ B M, ctx𝔹 B -> ctx𝕄 M -> ctx𝕄 (B ∘ M)
  | consℝ : ∀ R M, ctxℝ R -> ctx𝕄 M -> ctx𝕄 (R ∘ M)

inductive ctx𝔼 : Ctx -> Prop where
  | hole : ctx𝔼 (fun X => X)
  | cons𝔹 : ∀ B E, ctx𝔹 B -> ctx𝔼 E -> ctx𝔼 (B ∘ E)

mutual
  inductive ctxℙ : Ctx -> Prop where
    | hole : ctxℙ (fun X => X)
    | cons𝔹 : ∀ B Q, ctx𝔹 B -> ctxℚ Q -> ctxℙ (B ∘ Q)
    | consℝ : ∀ R P, ctxℝ R -> ctxℙ P -> ctxℙ (R ∘ P)
  inductive ctxℚ : Ctx -> Prop where
    | cons𝔹 : ∀ B Q, ctx𝔹 B -> ctxℚ Q -> ctxℚ (B ∘ Q)
    | consℝ : ∀ R P, ctxℝ R -> ctxℙ P -> ctxℚ (R ∘ P)
end

inductive step : Expr -> Expr -> Prop where
  | lets : ∀ M e v, ctx𝕄 M ->
    --lc (.lets v e) ->
    value v ->
    --x ∉ fv e ->
    step M⟦.lets v e⟧ M⟦openSubst v e⟧
  | app₁ : ∀ M e v, ctx𝕄 M ->
    --lc (.lam₁ e) ->
    value v ->
    --x ∉ fv e ->
    step M⟦.app₁ (.lam₁ e) v⟧ M⟦openSubst v e⟧
  | app₂ : ∀ M f arg, ctx𝕄 M ->
    step M⟦.app₂ (.code f) (.code arg)⟧ M⟦.reflect (.app₁ f arg)⟧
  | plus₁ : ∀ M l r, ctx𝕄 M ->
    step M⟦.plus₁ (.lit₁ l) (.lit₁ r)⟧ M⟦.lit₁ (l + r)⟧
  | plus₂ : ∀ M l r, ctx𝕄 M ->
    step M⟦.plus₂ (.code l) (.code r)⟧ M⟦.reflect (.plus₁ l r)⟧
  | lit₂ : ∀ M n, ctx𝕄 M ->
    step M⟦.lit₂ n⟧ M⟦.code (.lit₁ n)⟧
  | lam₂ : ∀ M e, ctx𝕄 M ->
    --x ∉ fv e ->
    step M⟦.lam₂ e⟧ M⟦.lam𝕔 (close₀ 0 (subst 0 (.code (.fvar 0)) (open₀ 0 e)))⟧
  | lam𝕔 : ∀ M e, ctx𝕄 M ->
    step M⟦.lam𝕔 (.code e)⟧ M⟦.reflect (.lam₁ e)⟧
  | reflect : ∀ P E b,
    ctxℙ P -> ctx𝔼 E ->
    step P⟦E⟦.reflect b⟧⟧ P⟦.let𝕔 b E⟦.code (.bvar 0)⟧⟧
  | let𝕔 : ∀ M b e, ctx𝕄 M ->
    step M⟦.let𝕔 b (.code e)⟧ M⟦.code (.lets b e)⟧

inductive stepn : Expr → Expr → Prop
| refl  : ∀ e, stepn e e
| multi : ∀ e₁ e₂ e₃, stepn e₁ e₂ → step e₂ e₃ → stepn e₁ e₃
