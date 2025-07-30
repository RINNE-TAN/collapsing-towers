import CollapsingTowers.TwoLevelRec.Syntax.Effect

inductive Stage : Type where
  | stat
  | dyn

notation:max "𝟙" => Stage.stat

notation:max "𝟚" => Stage.dyn

inductive Ty : Type where
  | nat
  | arrow (τ𝕒 : Ty) (τ𝕓 : Ty) (φ : Effect)
  | fragment (τ : Ty)
  | rep (τ : Ty)

inductive Expr : Type where
  | bvar (i : ℕ)
  | fvar (x : ℕ)
  | fix (e : Expr)
  | app₁ (f : Expr) (arg : Expr)
  | app₂ (f : Expr) (arg : Expr)
  | lit (n : ℕ)
  | lift (e : Expr)
  | run (e : Expr)
  | code (e : Expr)
  | reflect (e : Expr)
  | fix𝕔 (e : Expr)
  | lets (b : Expr) (e : Expr)
  | lets𝕔 (b : Expr) (e : Expr)
