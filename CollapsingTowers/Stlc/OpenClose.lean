
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.EquivFin
import CollapsingTowers.Stlc.Basic
@[simp]
def subst (x : ℕ) (v : Expr) : Expr -> Expr
  | .bvar i => .bvar i
  | .fvar y => if x == y then v else .fvar y
  | .lam e => .lam (subst x v e)
  | .app f arg => .app (subst x v f) (subst x v arg)
  | .unit => .unit

@[simp]
def openRec (n : ℕ) (v : Expr) : Expr -> Expr
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
  | lc_lam : (L : Finset ℕ) -> (∀ x, x ∉ L -> lc (open₀ (.fvar x) e)) -> lc (.lam e)
  | lc_app : lc f -> lc arg -> lc (.app f arg)
  | lc_unit : lc .unit

theorem subst_fresh : x ∉ fv e -> subst x v e = e := by
  intro Hnotfv
  induction e with
  | bvar => simp
  | fvar x =>
    simp at *
    intro HEqx
    contradiction
  | lam e IHe =>
    simp at *
    apply IHe
    apply Hnotfv
  | app f arg IHf IHarg =>
    simp at *
    constructor
    apply IHf
    apply Hnotfv.left
    apply IHarg
    apply Hnotfv.right
  | unit => simp

theorem subst_intro : x ∉ fv e -> subst x v (openRec n (.fvar x) e) = openRec n v e :=
  by
  intro Hnotfv
  induction e generalizing n with
  | bvar i =>
    if HEq : n = i then
      rw [HEq]
      simp
    else
      simp
      rw [if_neg HEq]
      rw [if_neg HEq]
      simp
  | fvar x =>
    simp at *
    intro HEq
    contradiction
  | lam e IHe =>
    simp at *
    apply IHe
    apply Hnotfv
  | app f arg IHf IHarg =>
    simp at *
    constructor
    apply IHf
    apply Hnotfv.left
    apply IHarg
    apply Hnotfv.right
  | unit => simp

theorem open_lc : lc e -> e = openRec n (.fvar y) e := by
  intro Hlc
  induction Hlc generalizing n with
  | lc_fvar => simp
  | lc_lam L _ IHe =>
    simp at *
    have ⟨fresh, Hfresh⟩ : ∃ x : ℕ, x ∉ L := by exact Infinite.exists_not_mem_finset L
    have IHe := @IHe fresh Hfresh
    admit
  | lc_app _ _ IHf IHarg =>
    simp at *
    constructor
    apply IHf
    apply IHarg
  | lc_unit => simp

theorem subst_open_var : ¬x = y -> lc v -> subst x v (openRec n (.fvar y) e) = openRec n (.fvar y) (subst x v e) :=
  by
  intro HNe Hlc
  induction e generalizing n with
  | fvar x₀ =>
    if HEq : x = x₀ then
      rw [HEq]
      simp
      apply open_lc
      apply Hlc
    else
      simp
      rw [if_neg HEq]
      simp
  | bvar i =>
    if HEq : n = i then
      rw [HEq]
      simp
      intro
      contradiction
    else
      simp
      rw [if_neg HEq]
      simp
  | lam _ IHe =>
    simp at *
    apply IHe
  | app _ _ IHf IHarg =>
    simp at *
    constructor
    apply IHf
    apply IHarg
  | unit => simp
