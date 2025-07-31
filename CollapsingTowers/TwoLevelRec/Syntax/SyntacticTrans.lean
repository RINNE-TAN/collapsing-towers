import CollapsingTowers.TwoLevelRec.Syntax.Basic

@[simp]
def opening (i : ℕ) (v : Expr) : Expr → Expr
  | .bvar j => if j = i then v else .bvar j
  | .fvar x => .fvar x
  | .fix e => .fix (opening (i + 2) v e)
  | .lift e => .lift (opening i v e)
  | .app₁ f arg => .app₁ (opening i v f) (opening i v arg)
  | .app₂ f arg => .app₂ (opening i v f) (opening i v arg)
  | .lit n => .lit n
  | .run e => .run (opening i v e)
  | .code e => .code (opening i v e)
  | .reflect e => .reflect (opening i v e)
  | .fix𝕔 e => .fix𝕔 (opening (i + 2) v e)
  | .lets b e => .lets (opening i v b) (opening (i + 1) v e)
  | .lets𝕔 b e => .lets𝕔 (opening i v b) (opening (i + 1) v e)

notation:max "{" i " ↦ " x "}" e => opening i (Expr.fvar x) e

@[simp]
def closing (i : ℕ) (x : ℕ) : Expr → Expr
  | .bvar j => .bvar j
  | .fvar y => if x == y then .bvar i else .fvar y
  | .fix e => .fix (closing (i + 2) x e)
  | .lift e => .lift (closing i x e)
  | .app₁ f arg => .app₁ (closing i x f) (closing i x arg)
  | .app₂ f arg => .app₂ (closing i x f) (closing i x arg)
  | .lit n => .lit n
  | .run e => .run (closing i x e)
  | .code e => .code (closing i x e)
  | .reflect e => .reflect (closing i x e)
  | .fix𝕔 e => .fix𝕔 (closing (i + 2) x e)
  | .lets b e => .lets (closing i x b) (closing (i + 1) x e)
  | .lets𝕔 b e => .lets𝕔 (closing i x b) (closing (i + 1) x e)

notation:max "{" i " ↤ " x "}" e => closing i x e

@[simp]
def subst (x : ℕ) (v : Expr) : Expr → Expr
  | .bvar i => .bvar i
  | .fvar y => if x = y then v else .fvar y
  | .fix e => .fix (subst x v e)
  | .lift e => .lift (subst x v e)
  | .app₁ f arg => .app₁ (subst x v f) (subst x v arg)
  | .app₂ f arg => .app₂ (subst x v f) (subst x v arg)
  | .lit n => .lit n
  | .run e => .run (subst x v e)
  | .code e => .code (subst x v e)
  | .reflect e => .reflect (subst x v e)
  | .fix𝕔 e => .fix𝕔 (subst x v e)
  | .lets b e => .lets (subst x v b) (subst x v e)
  | .lets𝕔 b e => .lets𝕔 (subst x v b) (subst x v e)

@[simp]
def maping𝕔 (i : ℕ) (e : Expr) : Expr :=
  match e with
  | .bvar j => if j == i then (.code (.bvar i)) else .bvar j
  | .fvar x => .fvar x
  | .fix e => .fix (maping𝕔 (i + 2) e)
  | .lift e => .lift (maping𝕔 i e)
  | .app₁ f arg => .app₁ (maping𝕔 i f) (maping𝕔 i arg)
  | .app₂ f arg => .app₂ (maping𝕔 i f) (maping𝕔 i arg)
  | .lit n => .lit n
  | .run e => .run (maping𝕔 i e)
  | .code e => .code (maping𝕔 i e)
  | .reflect e => .reflect (maping𝕔 i e)
  | .fix𝕔 e => .fix𝕔 (maping𝕔 (i + 2) e)
  | .lets b e => .lets (maping𝕔 i b) (maping𝕔 (i + 1) e)
  | .lets𝕔 b e => .lets𝕔 (maping𝕔 i b) (maping𝕔 (i + 1) e)

@[simp]
def shiftl_at (x : ℕ) (n : ℕ) : Expr → Expr
  | .bvar i => .bvar i
  | .fvar y => if x ≤ y then .fvar (y + n) else .fvar y
  | .fix e => .fix (shiftl_at x n e)
  | .lift e => .lift (shiftl_at x n e)
  | .app₁ f arg => .app₁ (shiftl_at x n f) (shiftl_at x n arg)
  | .app₂ f arg => .app₂ (shiftl_at x n f) (shiftl_at x n arg)
  | .lit n => .lit n
  | .run e => .run (shiftl_at x n e)
  | .code e => .code (shiftl_at x n e)
  | .reflect e => .reflect (shiftl_at x n e)
  | .fix𝕔 e => .fix𝕔 (shiftl_at x n e)
  | .lets b e => .lets (shiftl_at x n b) (shiftl_at x n e)
  | .lets𝕔 b e => .lets𝕔 (shiftl_at x n b) (shiftl_at x n e)

@[simp]
def shiftr_at (x : ℕ) : Expr → Expr
  | .bvar i => .bvar i
  | .fvar y => if x < y then .fvar (y - 1) else .fvar y
  | .fix e => .fix (shiftr_at x e)
  | .lift e => .lift (shiftr_at x e)
  | .app₁ f arg => .app₁ (shiftr_at x f) (shiftr_at x arg)
  | .app₂ f arg => .app₂ (shiftr_at x f) (shiftr_at x arg)
  | .lit n => .lit n
  | .run e => .run (shiftr_at x e)
  | .code e => .code (shiftr_at x e)
  | .reflect e => .reflect (shiftr_at x e)
  | .fix𝕔 e => .fix𝕔 (shiftr_at x e)
  | .lets b e => .lets (shiftr_at x b) (shiftr_at x e)
  | .lets𝕔 b e => .lets𝕔 (shiftr_at x b) (shiftr_at x e)

@[simp]
def expr.erase : Expr → Expr
  | .bvar i => .bvar i
  | .fvar y => .fvar y
  | .fix e => .fix (erase e)
  | .lift e => erase e
  | .app₁ f arg => .app₁ (erase f) (erase arg)
  | .app₂ f arg => .app₁ (erase f) (erase arg)
  | .lit n => .lit n
  | .run e => erase e
  | .code e => erase e
  | .reflect e => erase e
  | .fix𝕔 e => .fix (erase e)
  | .lets b e => .lets (erase b) (erase e)
  | .lets𝕔 b e => .lets (erase b) (erase e)

notation:max "‖" e "‖" => expr.erase e

abbrev Subst :=
  List Expr

@[simp]
def multi_subst : Subst → Expr → Expr
  | [], e => e
  | v :: γ, e => multi_subst γ (subst γ.length v e)

@[simp]
lemma multi_subst.fvar: ∀ γ x, x ≥ γ.length → multi_subst γ (.fvar x) = .fvar x :=
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
lemma multi_subst.app₁ : ∀ γ f arg, multi_subst γ (.app₁ f arg) = .app₁ (multi_subst γ f) (multi_subst γ arg) :=
  by
  intros γ f arg
  induction γ generalizing f arg
  case nil => rfl
  case cons IH => simp [IH]

@[simp]
lemma multi_subst.fix : ∀ γ e, multi_subst γ (.fix e) = .fix (multi_subst γ e) :=
  by
  intros γ e
  induction γ generalizing e
  case nil => rfl
  case cons IH => simp [IH]

@[simp]
lemma multi_subst.lit : ∀ γ n, multi_subst γ (.lit n) = .lit n :=
  by
  intros γ n
  induction γ
  case nil => rfl
  case cons IH => simp [IH]

@[simp]
lemma multi_subst.lets : ∀ γ b e, multi_subst γ (.lets b e) = .lets (multi_subst γ b) (multi_subst γ e) :=
  by
  intros γ b e
  induction γ generalizing b e
  case nil => rfl
  case cons IH => simp [IH]
