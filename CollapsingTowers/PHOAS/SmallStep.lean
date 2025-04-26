
import CollapsingTowers.PHOAS.Basic
def squash : Expr₀ (Expr₀ 𝕍) -> Expr₀ 𝕍
  | .var₀ x => x
  | .lam₀ e => .lam₀ (fun x => squash (e (.var₀ x)))
  | .app₀ f arg => .app₀ (squash f) (squash arg)
  | .unit₀ => .unit₀

def subst (e : {𝕍 : Type} -> 𝕍 -> Expr₀ 𝕍) (s : Expr) : Expr :=
  squash (e s)

abbrev Ctx :=
  Expr -> Expr

notation:max a "⟦" b "⟧" => a b

inductive ctx𝔹 : Ctx -> Prop where
  | appL : ∀ arg, ctx𝔹 (fun X => app X arg)
  | appR : ∀ v, value v -> ctx𝔹 (fun X => app v X)

inductive ctx𝕄 : Ctx -> Prop where
  | hole : ctx𝕄 id
  | 𝔹 : ∀ B M, ctx𝔹 B -> ctx𝕄 M -> ctx𝕄 (B ∘ M)

inductive step : Expr -> Expr -> Prop where
  | appβ : ∀ M v e, ctx𝕄 M -> value v -> step M⟦app (lam e) v⟧ M⟦subst e v⟧
