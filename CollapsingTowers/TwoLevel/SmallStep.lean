
import CollapsingTowers.TwoLevel.Basic
import CollapsingTowers.TwoLevel.OpenClose
abbrev Ctx :=
  Expr -> Expr

notation:max a "⟦" b "⟧" => a b

inductive ctx𝔹 : Ctx -> Prop where
  | appl₁ : ∀ arg, lc arg -> ctx𝔹 (fun X => .app₁ X arg)
  | appr₁ : ∀ v, value v -> ctx𝔹 (fun X => .app₁ v X)
  | appl₂ : ∀ arg, lc arg -> ctx𝔹 (fun X => .app₂ X arg)
  | appr₂ : ∀ v, value v -> ctx𝔹 (fun X => .app₂ v X)

inductive ctxℝ : Ctx -> Prop where
  | lam𝕔 : ctxℝ (fun X => .lam𝕔 X)
  | let𝕔 : ∀ e, ctxℝ (fun X => .let𝕔 e X)

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
  | app₁ : ∀ M e v, ctx𝕄 M -> lc (.lam₁ e) -> value v -> step M⟦.app₁ (.lam₁ e) v⟧ M⟦open₀ v e⟧
  | app₂ : ∀ M f arg, ctx𝕄 M -> step M⟦.app₂ (.code f) (.code arg)⟧ M⟦.reflect (.app₁ f arg)⟧
  | lit₂ : ∀ M n, ctx𝕄 M -> step M⟦.lit₂ n⟧ M⟦.code (.lit₁ n)⟧
  |
  lam₂ :
    ∀ M e x, ctx𝕄 M -> x ∉ fv e -> step M⟦.lam₂ e⟧ M⟦.lam𝕔 (close₀ x (subst x (.code (.fvar x)) (open₀ (.fvar x) e)))⟧
  | lam𝕔 : ∀ M e, ctx𝕄 M -> step M⟦.lam𝕔 (.code e)⟧ M⟦.reflect (.lam₁ e)⟧
