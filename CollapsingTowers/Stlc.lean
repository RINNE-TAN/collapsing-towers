
inductive Expr : Type where
  | Var (x : String)
  | Lam (x : String) (e : Expr)
  | App (f : Expr) (arg : Expr)

inductive value : Expr -> Prop where
  | value_lam : value (.Lam x e)

abbrev Ctx :=
  Expr -> Expr

notation:max a "⟦" b "⟧" => a b

inductive ctx𝔹 : Ctx -> Prop where
  | ctx𝔹_appL : ctx𝔹 (fun X => .App X arg)
  | ctx𝔹_appR : value v -> ctx𝔹 (fun X => .App v X)

inductive ctx𝕄 : Ctx -> Prop where
  | ctx𝕄_hole : ctx𝕄 (fun X => X)
  | ctx𝕄_𝔹 : ctx𝔹 B -> ctx𝕄 M -> ctx𝕄 (B ∘ M)

def subst (x : String) (v : Expr) (e : Expr) : Expr :=
  match e with
  | .Var y => if x == y then v else .Var y
  | .Lam y e => if x == y then .Lam y e else .Lam y (subst x v e)
  | .App f arg => .App (subst x v f) (subst x v arg)

inductive step : Expr -> Expr -> Prop where
  | step_appβ : ctx𝕄 M -> value v -> step M⟦.App (.Lam x e) v⟧ M⟦subst x v e⟧

theorem step_decidable : step e₀ e₁ -> step e₀ e₂ -> e₁ = e₂ := by admit
