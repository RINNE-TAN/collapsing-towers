
import CollapsingTowers.Stlc.Basic
@[simp]
def subst (x : String) (v : Expr) : Expr -> Expr
  | .bvar i => .bvar i
  | .fvar y => if x == y then v else .fvar y
  | .lam e => .lam (subst x v e)
  | .app f arg => .app (subst x v f) (subst x v arg)
  | .unit => .unit

@[simp]
def openRec (n : Nat) (v : Expr) : Expr -> Expr
  | .bvar i => if n == i then v else .bvar i
  | .fvar x => .fvar x
  | .lam e => .lam (openRec (n + 1) v e)
  | .app f arg => .app (openRec n v f) (openRec n v arg)
  | .unit => .unit

@[simp]
def open₀ (v : Expr) : Expr -> Expr :=
  openRec 0 v

inductive lc : Expr -> Prop where
  | lc_fvar : lc (.fvar x)
  | lc_lam : lc (open₀ e x) -> lc (.lam e)
  | lc_app : lc f -> lc arg -> lc (.app f arg)
  | lc_unit : lc .unit
