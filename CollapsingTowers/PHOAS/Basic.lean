
inductive Ty : Type where
  | unit
  | arrow : Ty -> Ty -> Ty

inductive Expr₀ (𝕍 : Type) : Type where
  | var₀ (x : 𝕍)
  | lam₀ (e : 𝕍 -> Expr₀ 𝕍)
  | app₀ (f : Expr₀ 𝕍) (arg : Expr₀ 𝕍)
  | unit₀

def Expr :=
  {𝕍 : Type} -> Expr₀ 𝕍

def var (x : {𝕍 : Type} -> 𝕍) : Expr :=
  .var₀ x

def lam (e : {𝕍 : Type} -> 𝕍 -> Expr₀ 𝕍) : Expr :=
  .lam₀ e

def app (f : Expr) (arg : Expr) : Expr :=
  .app₀ f arg

def unit : Expr :=
  .unit₀

inductive value : Expr -> Prop where
  | lam : ∀ e, value (lam e)
  | unit : value (unit)

def apply𝕍 (e : {𝕍 : Type} -> 𝕍 -> Expr₀ 𝕍) (x : {𝕍 : Type} -> 𝕍) : Expr :=
  e x
