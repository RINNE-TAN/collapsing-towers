import Instar.TwoLevelBasic.Syntax.Basic

@[simp]
def opening (i : ℕ) (v : Expr) : Expr → Expr
  | .bvar j => if j = i then v else .bvar j
  | .fvar x => .fvar x
  | .lam e => .lam (opening (i + 1) v e)
  | .lift e => .lift (opening i v e)
  | .app₁ f arg => .app₁ (opening i v f) (opening i v arg)
  | .app₂ f arg => .app₂ (opening i v f) (opening i v arg)
  | .lit n => .lit n
  | .run e => .run (opening i v e)
  | .code e => .code (opening i v e)
  | .reflect e => .reflect (opening i v e)
  | .lam𝕔 e => .lam𝕔 (opening (i + 1) v e)
  | .lets b e => .lets (opening i v b) (opening (i + 1) v e)
  | .lets𝕔 b e => .lets𝕔 (opening i v b) (opening (i + 1) v e)

notation:max "{" i " ↦ " x "}" e => opening i (Expr.fvar x) e

@[simp]
def closing (i : ℕ) (x : ℕ) : Expr → Expr
  | .bvar j => .bvar j
  | .fvar y => if x == y then .bvar i else .fvar y
  | .lam e => .lam (closing (i + 1) x e)
  | .lift e => .lift (closing i x e)
  | .app₁ f arg => .app₁ (closing i x f) (closing i x arg)
  | .app₂ f arg => .app₂ (closing i x f) (closing i x arg)
  | .lit n => .lit n
  | .run e => .run (closing i x e)
  | .code e => .code (closing i x e)
  | .reflect e => .reflect (closing i x e)
  | .lam𝕔 e => .lam𝕔 (closing (i + 1) x e)
  | .lets b e => .lets (closing i x b) (closing (i + 1) x e)
  | .lets𝕔 b e => .lets𝕔 (closing i x b) (closing (i + 1) x e)

notation:max "{" i " ↤ " x "}" e => closing i x e

@[simp]
def subst (x : ℕ) (v : Expr) : Expr → Expr
  | .bvar i => .bvar i
  | .fvar y => if x = y then v else .fvar y
  | .lam e => .lam (subst x v e)
  | .lift e => .lift (subst x v e)
  | .app₁ f arg => .app₁ (subst x v f) (subst x v arg)
  | .app₂ f arg => .app₂ (subst x v f) (subst x v arg)
  | .lit n => .lit n
  | .run e => .run (subst x v e)
  | .code e => .code (subst x v e)
  | .reflect e => .reflect (subst x v e)
  | .lam𝕔 e => .lam𝕔 (subst x v e)
  | .lets b e => .lets (subst x v b) (subst x v e)
  | .lets𝕔 b e => .lets𝕔 (subst x v b) (subst x v e)

@[simp]
def codify (i : ℕ) (e : Expr) : Expr :=
  match e with
  | .bvar j => if j == i then (.code (.bvar i)) else .bvar j
  | .fvar x => .fvar x
  | .lam e => .lam (codify (i + 1) e)
  | .lift e => .lift (codify i e)
  | .app₁ f arg => .app₁ (codify i f) (codify i arg)
  | .app₂ f arg => .app₂ (codify i f) (codify i arg)
  | .lit n => .lit n
  | .run e => .run (codify i e)
  | .code e => .code (codify i e)
  | .reflect e => .reflect (codify i e)
  | .lam𝕔 e => .lam𝕔 (codify (i + 1) e)
  | .lets b e => .lets (codify i b) (codify (i + 1) e)
  | .lets𝕔 b e => .lets𝕔 (codify i b) (codify (i + 1) e)

@[simp]
def shiftl (x : ℕ) (n : ℕ) : Expr → Expr
  | .bvar i => .bvar i
  | .fvar y => if x ≤ y then .fvar (y + n) else .fvar y
  | .lam e => .lam (shiftl x n e)
  | .lift e => .lift (shiftl x n e)
  | .app₁ f arg => .app₁ (shiftl x n f) (shiftl x n arg)
  | .app₂ f arg => .app₂ (shiftl x n f) (shiftl x n arg)
  | .lit n => .lit n
  | .run e => .run (shiftl x n e)
  | .code e => .code (shiftl x n e)
  | .reflect e => .reflect (shiftl x n e)
  | .lam𝕔 e => .lam𝕔 (shiftl x n e)
  | .lets b e => .lets (shiftl x n b) (shiftl x n e)
  | .lets𝕔 b e => .lets𝕔 (shiftl x n b) (shiftl x n e)

@[simp]
def shiftr (x : ℕ) : Expr → Expr
  | .bvar i => .bvar i
  | .fvar y => if x < y then .fvar (y - 1) else .fvar y
  | .lam e => .lam (shiftr x e)
  | .lift e => .lift (shiftr x e)
  | .app₁ f arg => .app₁ (shiftr x f) (shiftr x arg)
  | .app₂ f arg => .app₂ (shiftr x f) (shiftr x arg)
  | .lit n => .lit n
  | .run e => .run (shiftr x e)
  | .code e => .code (shiftr x e)
  | .reflect e => .reflect (shiftr x e)
  | .lam𝕔 e => .lam𝕔 (shiftr x e)
  | .lets b e => .lets (shiftr x b) (shiftr x e)
  | .lets𝕔 b e => .lets𝕔 (shiftr x b) (shiftr x e)

@[simp]
def erase : Expr → Expr
  | .bvar i => .bvar i
  | .fvar y => .fvar y
  | .lam e => .lam (erase e)
  | .lift e => erase e
  | .app₁ f arg => .app₁ (erase f) (erase arg)
  | .app₂ f arg => .app₁ (erase f) (erase arg)
  | .lit n => .lit n
  | .run e => erase e
  | .code e => erase e
  | .reflect e => erase e
  | .lam𝕔 e => .lam (erase e)
  | .lets b e => .lets (erase b) (erase e)
  | .lets𝕔 b e => .lets (erase b) (erase e)

notation:max "⎸" e "⎹" => erase e

abbrev Subst :=
  List Expr

@[simp]
def msubst : Subst → Expr → Expr
  | [], e => e
  | v :: γ, e => msubst γ (subst γ.length v e)

@[simp]
lemma msubst.bvar: ∀ γ i, msubst γ (.bvar i) = .bvar i :=
  by
  intros γ i
  induction γ
  case nil => rfl
  case cons IH => simp [IH]

@[simp]
lemma msubst.fvar: ∀ γ x, x ≥ γ.length → msubst γ (.fvar x) = .fvar x :=
  by
  intros γ x HGe
  induction γ
  case nil => rfl
  case cons tail IH =>
    simp at HGe
    by_cases HEq : tail.length = x
    . omega
    . simp [if_neg HEq]
      apply IH; omega

@[simp]
lemma msubst.lam : ∀ γ e, msubst γ (.lam e) = .lam (msubst γ e) :=
  by
  intros γ e
  induction γ generalizing e
  case nil => rfl
  case cons IH => simp [IH]

@[simp]
lemma msubst.app₁ : ∀ γ f arg, msubst γ (.app₁ f arg) = .app₁ (msubst γ f) (msubst γ arg) :=
  by
  intros γ f arg
  induction γ generalizing f arg
  case nil => rfl
  case cons IH => simp [IH]

@[simp]
lemma msubst.lit : ∀ γ n, msubst γ (.lit n) = .lit n :=
  by
  intros γ n
  induction γ
  case nil => rfl
  case cons IH => simp [IH]

@[simp]
lemma msubst.lets : ∀ γ b e, msubst γ (.lets b e) = .lets (msubst γ b) (msubst γ e) :=
  by
  intros γ b e
  induction γ generalizing b e
  case nil => rfl
  case cons IH => simp [IH]
