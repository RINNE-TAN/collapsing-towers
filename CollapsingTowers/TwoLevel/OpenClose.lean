
import CollapsingTowers.TwoLevel.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Max
@[simp]
def fv : Expr → Finset ℕ
  | .bvar _ => ∅
  | .fvar y => { y }
  | .lam₁ _ e => fv e
  | .lam₂ _ e => fv e
  | .app₁ f arg => fv f ∪ fv arg
  | .app₂ f arg => fv f ∪ fv arg
  | .lit₁ _ => ∅
  | .lit₂ _ => ∅
  | .plus₁ l r => fv l ∪ fv r
  | .plus₂ l r => fv l ∪ fv r
  | .code e => fv e
  | .reflect e => fv e
  | .lam𝕔 _ e => fv e
  | .lets b e => fv b ∪ fv e
  | .let𝕔 b e => fv b ∪ fv e

@[simp]
def fresh (e : Expr) : ℕ :=
  (fv e).max.elim 0 .succ

@[simp]
def subst (x : ℕ) (v : Expr) : Expr -> Expr
  | .bvar i => .bvar i
  | .fvar y => if x = y then v else .fvar y
  | .lam₁ τ e => .lam₁ τ (subst x v e)
  | .lam₂ τ e => .lam₂ τ (subst x v e)
  | .app₁ f arg => .app₁ (subst x v f) (subst x v arg)
  | .app₂ f arg => .app₂ (subst x v f) (subst x v arg)
  | .lit₁ n => .lit₁ n
  | .lit₂ n => .lit₂ n
  | .plus₁ l r => .plus₁ (subst x v l) (subst x v r)
  | .plus₂ l r => .plus₂ (subst x v l) (subst x v r)
  | .code e => .code (subst x v e)
  | .reflect e => .reflect (subst x v e)
  | .lam𝕔 τ e => .lam𝕔 τ (subst x v e)
  | .lets b e => .lets (subst x v b) (subst x v e)
  | .let𝕔 b e => .let𝕔 (subst x v b) (subst x v e)

-- opening i t1 t2 = [i -> t1]t2
@[simp]
def opening (i : ℕ) (x : Expr) : Expr -> Expr
  | .bvar j => if j = i then x else .bvar j
  | .fvar x => .fvar x
  | .lam₁ τ e => .lam₁ τ (opening (i + 1) x e)
  | .lam₂ τ e => .lam₂ τ (opening (i + 1) x e)
  | .app₁ f arg => .app₁ (opening i x f) (opening i x arg)
  | .app₂ f arg => .app₂ (opening i x f) (opening i x arg)
  | .lit₁ n => .lit₁ n
  | .lit₂ n => .lit₂ n
  | .plus₁ l r => .plus₁ (opening i x l) (opening i x r)
  | .plus₂ l r => .plus₂ (opening i x l) (opening i x r)
  | .code e => .code (opening i x e)
  | .reflect e => .reflect (opening i x e)
  | .lam𝕔 τ e => .lam𝕔 τ (opening (i + 1) x e)
  | .lets b e => .lets (opening i x b) (opening (i + 1) x e)
  | .let𝕔 b e => .let𝕔 (opening i x b) (opening (i + 1) x e)

@[simp]
def open₀ (x : ℕ) : Expr -> Expr :=
  opening 0 (.fvar x)

@[simp]
def open_subst (tgt : Expr) (within : Expr) :=
  opening 0 tgt within

@[simp]
def closing (i : ℕ) (x : ℕ) : Expr -> Expr
  | .bvar j => .bvar j
  | .fvar y => if x == y then .bvar i else .fvar y
  | .lam₁ τ e => .lam₁ τ (closing (i + 1) x e)
  | .lam₂ τ e => .lam₂ τ (closing (i + 1) x e)
  | .app₁ f arg => .app₁ (closing i x f) (closing i x arg)
  | .app₂ f arg => .app₂ (closing i x f) (closing i x arg)
  | .lit₁ n => .lit₁ n
  | .lit₂ n => .lit₂ n
  | .plus₁ l r => .plus₁ (closing i x l) (closing i x r)
  | .plus₂ l r => .plus₂ (closing i x l) (closing i x r)
  | .code e => .code (closing i x e)
  | .reflect e => .reflect (closing i x e)
  | .lam𝕔 τ e => .lam𝕔 τ (closing (i + 1) x e)
  | .lets b e => .lets (closing i x b) (closing (i + 1) x e)
  | .let𝕔 b e => .let𝕔 (closing i x b) (closing (i + 1) x e)

@[simp]
def close₀ : ℕ -> Expr -> Expr :=
  closing 0

/--
inductive lc : Expr -> Prop where
  | fvar : ∀ x, lc (.fvar x)
  | lam₁ : ∀ e x, lc (open₀ x e) -> lc (.lam₁ e)
  | lam₂ : ∀ e x, lc (open₀ x e) -> lc (.lam₂ e)
  | app₁ : ∀ f arg, lc f -> lc arg -> lc (.app₁ f arg)
  | app₂ : ∀ f arg, lc f -> lc arg -> lc (.app₂ f arg)
  | lit₁ : ∀ n, lc (.lit₁ n)
  | lit₂ : ∀ n, lc (.lit₂ n)
  | plus₁ : ∀ l r, lc l -> lc r -> lc (.plus₁ l r)
  | plus₂ : ∀ l r, lc l -> lc r -> lc (.plus₂ l r)
  | code : ∀ e, lc e -> lc (.code e)
  | reflect : ∀ e, lc e -> lc (.reflect e)
  | lam𝕔 : ∀ e x, lc (open₀ x e) -> lc (.lam𝕔 e)
  | lets : ∀ b e x, lc b -> lc (open₀ x e) -> lc (.lets b e)
  | let𝕔 : ∀ b e x, lc b -> lc (open₀ x e) -> lc (.let𝕔 b e)
-/

-- closedness condition for free variables
@[simp]
def closed_at (e : Expr) (f : ℕ) : Prop :=
  match e with
  | .bvar _ => true
  | .fvar x => x < f
  | .lam₁ _ e => closed_at e f
  | .lam₂ _ e => closed_at e f
  | .app₁ e1 e2 => closed_at e1 f ∧ closed_at e2 f
  | .app₂ e1 e2 => closed_at e1 f ∧ closed_at e2 f
  | .lit₁ _ => true
  | .lit₂ _ => true
  | .plus₁ l r => closed_at l f ∧ closed_at r f
  | .plus₂ l r => closed_at l f ∧ closed_at r f
  | .code e => closed_at e f
  | .reflect e => closed_at e f
  | .lam𝕔 _ e => closed_at e f
  | .lets b e => closed_at b f ∧ closed_at e f
  | .let𝕔 b e => closed_at b f ∧ closed_at e f

-- closedness condition for bound variables
@[simp]
def closedb_at (e : Expr) (b : ℕ) : Prop :=
  match e with
  | .bvar x => x < b
  | .fvar _ => true
  | .lam₁ _ e => closedb_at e (b + 1)
  | .lam₂ _ e => closedb_at e (b + 1)
  | .app₁ e1 e2 => closedb_at e1 b ∧ closedb_at e2 b
  | .app₂ e1 e2 => closedb_at e1 b ∧ closedb_at e2 b
  | .lit₁ _ => true
  | .lit₂ _ => true
  | .plus₁ l r => closedb_at l b ∧ closedb_at r b
  | .plus₂ l r => closedb_at l b ∧ closedb_at r b
  | .code e => closedb_at e b
  | .reflect e => closedb_at e b
  | .lam𝕔 _ e => closedb_at e (b + 1)
  | .lets e1 e2 => closedb_at e1 b ∧ closedb_at e2 (b + 1)
  | .let𝕔 e1 e2 => closedb_at e1 b ∧ closedb_at e2 (b + 1)

@[simp]
def lc e := closedb_at e 0

lemma subst_intro : ∀ x e v i, closed_at e x -> subst x v (opening i (.fvar x) e) = opening i v e :=
  by
  intros x e; induction e <;> intros v i Hclosed <;> simp at *
  case bvar j => by_cases HEq : j = i; simp [HEq]; simp [if_neg HEq]
  case fvar => omega
  case lam₁ _ IHe
  | lam₂ _ IHe
  | code _ IHe
  | reflect _ IHe
  | lam𝕔 _ IHe => apply IHe; apply Hclosed
  case app₁ _ _ ih1 ih2
  | app₂ _ _ ih1 ih2
  | plus₁ _ _ ih1 ih2
  | plus₂ _ _ ih1 ih2
  | lets _ _ ih1 ih2
  | let𝕔 _ _ ih1 ih2 => constructor; apply ih1; apply Hclosed.left; apply ih2; apply Hclosed.right

lemma subst_closed_id : ∀ x e v, closed_at e x -> subst x v e = e :=
  by
  intros x e v He
  induction e with
  | bvar => simp
  | fvar => simp at *; omega
  | lam₁ _ _ IH
  | lam₂ _ _ IH
  | lam𝕔 _ _ IH =>
    simp; apply IH; apply He
  | app₁ _ _ IH₀ IH₁
  | app₂ _ _ IH₀ IH₁
  | plus₁ _ _ IH₀ IH₁
  | plus₂ _ _ IH₀ IH₁ =>
    simp; constructor
    apply IH₀; apply He.left
    apply IH₁; apply He.right
  | lets _ _ IHb IHe
  | let𝕔 _ _ IHb IHe =>
    simp; constructor
    apply IHb; apply He.left
    apply IHe; apply He.right
  | code _ IH
  | reflect _ IH =>
    simp; apply IH; apply He
  | lit₁| lit₂ => simp

lemma openSubst_intro : ∀ x e v, closed_at e x -> subst x v (open₀ x e) = open_subst v e :=
  by
  intros _ _ _ Hclosed
  apply subst_intro
  apply Hclosed

lemma closedb_inc: ∀ t n n1,
    closedb_at t n -> n <= n1 ->
    closedb_at t n1 := by
  intros t; induction t <;> intros n n1 hcl hle <;> simp
  case bvar x => simp at hcl; omega
  case lam₁ t ih
     | lam₂ t ih
     | lam𝕔 t ih =>
    simp at hcl; apply ih; apply hcl; omega
  case app₁ t1 t2 ih1 ih2
     | app₂ t1 t2 ih1 ih2
     | plus₁ t1 t2 ih1 ih2
     | plus₂ t1 t2 ih1 ih2
     | lets t1 t2 ih1 ih2
     | let𝕔 t1 t2 ih1 ih2 =>
    apply And.intro
    . apply ih1; apply hcl.1; omega
    . apply ih2; apply hcl.2; omega
  case code t ih | reflect t ih =>
    apply ih; apply hcl; assumption

lemma closed_inc : ∀ x y e, closed_at e x -> x <= y -> closed_at e y :=
  by
  intros x y e Hclose Hxy
  induction e with
  | bvar j => simp
  | fvar z => simp at *; omega
  | app₁ _ _ IH₀ IH₁
  | app₂ _ _ IH₀ IH₁
  | plus₁ _ _ IH₀ IH₁
  | plus₂ _ _ IH₀ IH₁
  | lets _ _ IH₀ IH₁
  | let𝕔 _ _ IH₀ IH₁ =>
    simp; constructor
    apply IH₀; apply Hclose.left
    apply IH₁; apply Hclose.right
  | lit₁| lit₂ => simp
  | lam₁ _ _ IH
  | lam₂ _ _ IH
  | lam𝕔 _ _ IH
  | code _ IH
  | reflect _ IH =>
    simp; apply IH; apply Hclose

lemma subst_closedb_at : ∀ x e v i, closedb_at v i -> closedb_at e i -> closedb_at (subst x v e) i :=
  by
  intros x e v i Hv He
  induction e generalizing i with
  | bvar => apply He
  | fvar y =>
    by_cases HEq : x = y
    . rw [HEq]; simp; apply Hv
    . simp; rw [if_neg HEq]; simp
  | lam₁ _ _ IH
  | lam₂ _ _ IH
  | lam𝕔 _ _ IH =>
    apply IH; apply closedb_inc; apply Hv; omega; apply He
  | app₁ _ _ IH₀ IH₁
  | app₂ _ _ IH₀ IH₁
  | plus₁ _ _ IH₀ IH₁
  | plus₂ _ _ IH₀ IH₁ =>
    constructor
    apply IH₀; apply Hv; apply He.left
    apply IH₁; apply Hv; apply He.right
  | lets _ _ IHb IHe
  | let𝕔 _ _ IHb IHe =>
    constructor
    apply IHb; apply Hv; apply He.left
    apply IHe; apply closedb_inc; apply Hv; omega; apply He.right
  | code _ IH
  | reflect _ IH =>
    simp; apply IH; apply Hv; apply He
  | lit₁| lit₂ => simp

lemma subst_closed_at : ∀ x e v y, closed_at v y -> closed_at e y -> closed_at (subst x v e) y :=
  by
  intros x e v y Hv He
  induction e generalizing y with
  | bvar => apply He
  | fvar z =>
    by_cases HEq : x = z
    . rw [HEq]; simp; apply Hv
    . simp; rw [if_neg HEq]; apply He
  | lam₁ _ _ IH
  | lam₂ _ _ IH
  | lam𝕔 _ _ IH =>
    apply IH; apply Hv; apply He
  | app₁ _ _ IH₀ IH₁
  | app₂ _ _ IH₀ IH₁
  | plus₁ _ _ IH₀ IH₁
  | plus₂ _ _ IH₀ IH₁
  | lets _ _ IH₀ IH₁
  | let𝕔 _ _ IH₀ IH₁ =>
    constructor
    apply IH₀; apply Hv; apply He.left
    apply IH₁; apply Hv; apply He.right
  | code _ IH
  | reflect _ IH =>
    simp; apply IH; apply Hv; apply He
  | lit₁| lit₂ => simp

lemma subst_closed_at_dec : ∀ x e v, closed_at v x -> closed_at e (x + 1) -> closed_at (subst x v e) x :=
  by
  intros x e v Hv He
  induction e with
  | bvar => apply He
  | fvar z =>
    by_cases HEq : x = z
    . rw [← HEq]; simp; apply Hv
    . simp; rw [if_neg HEq]; simp at *; omega
  | lam₁ _ _ IH
  | lam₂ _ _ IH
  | lam𝕔 _ _ IH =>
    apply IH; apply He
  | app₁ _ _ IH₀ IH₁
  | app₂ _ _ IH₀ IH₁
  | plus₁ _ _ IH₀ IH₁
  | plus₂ _ _ IH₀ IH₁
  | lets _ _ IH₀ IH₁
  | let𝕔 _ _ IH₀ IH₁ =>
    constructor
    apply IH₀; apply He.left
    apply IH₁; apply He.right
  | code _ IH
  | reflect _ IH =>
    simp; apply IH; apply He
  | lit₁| lit₂ => simp

lemma open_closedb : ∀ t n m,
  closedb_at (opening m (.fvar n) t) m →
  closedb_at t (m + 1) := by
  intros t; induction t <;> intros n m h <;> simp
  case bvar x =>
    by_cases hx: (x = m)
    . omega
    . by_cases hx': (x < m)
      . omega;
      . simp at h; rw [if_neg hx] at h; simp at h; omega
  case lam₁ t ih
     | lam₂ t ih =>
    apply ih n (m + 1); simp at h; assumption
  case code _ ih
     | reflect _ ih
     | lam𝕔 _ ih =>
    simp at *; apply ih; apply h
  case app₁ t1 t2 ih1 ih2
     | app₂ t1 t2 ih1 ih2
     | plus₁ _ _ ih1 ih2
     | plus₂ _ _ ih1 ih2 =>
    apply And.intro; apply ih1 n m h.1; apply ih2 n m h.2
  case lets _ _ ih1 ih2
     | let𝕔 _ _ ih1 ih2 =>
    apply And.intro; apply ih1 n m h.1; apply ih2 n (m + 1) h.2

lemma open_closedb': ∀ t n m,
    closedb_at t (m + 1) → closedb_at (opening m (.fvar n) t) m := by
  intros t; induction t <;> intros n m h <;> simp
  case bvar x =>
    by_cases hx: (x = m)
    . simp [hx]
    . rw [if_neg hx]; simp at h; simp; omega
  case lam₁ t ih
     | lam₂ t ih =>
    apply ih n (m + 1); simp at h; assumption
  case code _ ih
     | reflect _ ih
     | lam𝕔 _ ih =>
    simp at *; apply ih; apply h
  case app₁ t1 t2 ih1 ih2
     | app₂ t1 t2 ih1 ih2
     | plus₁ _ _ ih1 ih2
     | plus₂ _ _ ih1 ih2 =>
    apply And.intro; apply ih1 n m h.1; apply ih2 n m h.2
  case lets _ _ ih1 ih2
     | let𝕔 _ _ ih1 ih2 =>
    apply And.intro; apply ih1 n m h.1; apply ih2 n (m + 1) h.2

theorem close_closed : ∀ e x i, closed_at e (x + 1) → closed_at (closing i x e) x :=
  by
  intros e x i
  induction e generalizing i with
  | fvar y =>
    by_cases HEq : x = y
    . rw [HEq]; simp
    . simp; rw [if_neg HEq]; simp; omega
  | bvar => simp
  | lam₁ _ _ IH
  | lam₂ _ _ IH
  | lam𝕔 _ _ IH
  | code _ IH
  | reflect _ IH => apply IH
  | app₁ _ _ IH₀ IH₁
  | app₂ _ _ IH₀ IH₁
  | plus₁ _ _ IH₀ IH₁
  | plus₂ _ _ IH₀ IH₁
  | lets _ _ IH₀ IH₁
  | let𝕔 _ _ IH₀ IH₁ =>
    intro Hclose; constructor
    apply IH₀; apply Hclose.left
    apply IH₁; apply Hclose.right
  | lit₁| lit₂ => simp

theorem open_closed : ∀ e x i, closed_at e x → closed_at (opening i (.fvar x) e) (x + 1) :=
  by
  intros e x i
  induction e generalizing i with
  | fvar y => simp; omega
  | bvar j =>
    by_cases HEq : j = i
    . rw [HEq]; simp
    . simp; rw [if_neg HEq]; simp
  | lam₁ _ _ IH
  | lam₂ _ _ IH
  | lam𝕔 _ _ IH
  | code _ IH
  | reflect _ IH => apply IH
  | app₁ _ _ IH₀ IH₁
  | app₂ _ _ IH₀ IH₁
  | plus₁ _ _ IH₀ IH₁
  | plus₂ _ _ IH₀ IH₁
  | lets _ _ IH₀ IH₁
  | let𝕔 _ _ IH₀ IH₁ =>
    intro Hclose; constructor
    apply IH₀; apply Hclose.left
    apply IH₁; apply Hclose.right
  | lit₁| lit₂ => simp

theorem close_closedb : ∀ e x i j, j < i -> closedb_at e i → closedb_at (closing j x e) i :=
  by
  intros e x i j Hlt
  induction e generalizing i j with
  | fvar y =>
    by_cases HEq : x = y
    . rw [HEq]; simp; omega
    . simp; rw [if_neg HEq]; simp
  | bvar => simp
  | lam₁ _ _ IH
  | lam₂ _ _ IH
  | lam𝕔 _ _ IH
  | code _ IH
  | reflect _ IH =>
    apply IH; omega
  | app₁ _ _ IH₀ IH₁
  | app₂ _ _ IH₀ IH₁
  | plus₁ _ _ IH₀ IH₁
  | plus₂ _ _ IH₀ IH₁
  | lets _ _ IH₀ IH₁
  | let𝕔 _ _ IH₀ IH₁ =>
    intro Hclose; constructor
    apply IH₀; omega; apply Hclose.left
    apply IH₁; omega; apply Hclose.right
  | lit₁| lit₂ => simp

lemma closedb_opening_id: ∀ t1 t2 n,
  closedb_at t1 n -> opening n t2 t1 = t1 := by
  intros t1; induction t1 <;> intros t2 n h <;> simp
  case bvar x => intro xn; simp at h; omega
  case lam₁ t ih
     | lam₂ t ih =>
    simp at h; apply ih; assumption
  case code _ ih
     | reflect _ ih
     | lam𝕔 _ ih =>
    simp at *; apply ih; apply h
  case app₁ t1 t2 ih1 ih2
     | app₂ t1 t2 ih1 ih2
     | plus₁ _ _ ih1 ih2
     | plus₂ _ _ ih1 ih2
     | lets _ _ ih1 ih2
     | let𝕔 _ _ ih1 ih2 =>
    apply And.intro; apply ih1; apply h.1; apply ih2; apply h.2

lemma open_close_id : ∀ i e x, closedb_at e i -> opening i (.fvar x) (closing i x e) = e :=
  by
  intros i e x Hlc
  induction e generalizing i with
  | bvar j =>
    simp
    intro HEq
    rw [HEq] at Hlc
    simp at Hlc
  | fvar y =>
    simp
    by_cases HEq : x = y
    . rw [HEq]; simp
    . rw [if_neg HEq]; simp
  | lam₁ _ _ IHe
  | lam₂ _ _ IHe
  | lam𝕔 _ _ IHe
  | code _ IHe
  | reflect _ IHe =>
    simp; apply IHe; apply Hlc
  | app₁ _ _ IH₀ IH₁
  | app₂ _ _ IH₀ IH₁
  | plus₁ _ _ IH₀ IH₁
  | plus₂ _ _ IH₀ IH₁
  | lets _ _ IH₀ IH₁
  | let𝕔 _ _ IH₀ IH₁ =>
    simp; constructor
    apply IH₀; apply Hlc.left
    apply IH₁; apply Hlc.right
  | lit₁| lit₂ => rfl

lemma open_close_id₀ : ∀ e x, lc e -> open₀ x (close₀ x e) = e := by apply open_close_id

lemma subst_opening_comm :
    ∀ x y e v i, x ≠ y -> closedb_at v i -> subst x v (opening i (.fvar y) e) = opening i (.fvar y) (subst x v e) :=
  by
  intro x y e v i HNe Hclosedb
  induction e generalizing i with
  | bvar j =>
    by_cases HEq : j = i
    . simp; rw [if_pos HEq]; simp; omega
    . simp; rw [if_neg HEq]; simp
  | fvar z =>
    by_cases HEq : x = z
    . simp; rw [if_pos HEq]; rw [closedb_opening_id]; apply Hclosedb
    . simp; rw [if_neg HEq]; simp
  | app₁ _ _ IH₀ IH₁
  | app₂ _ _ IH₀ IH₁
  | plus₁ _ _ IH₀ IH₁
  | plus₂ _ _ IH₀ IH₁ =>
    simp; constructor
    apply IH₀; apply Hclosedb
    apply IH₁; apply Hclosedb
  | lets _ _ IH₀ IH₁
  | let𝕔 _ _ IH₀ IH₁ =>
    simp; constructor
    apply IH₀; apply Hclosedb
    apply IH₁; apply closedb_inc; apply Hclosedb; omega
  | code _ IH
  | reflect _ IH =>
    simp; apply IH; apply Hclosedb
  | lit₁| lit₂ => simp
  | lam₁ _ _ IH
  | lam₂ _ _ IH
  | lam𝕔 _ _ IH =>
    simp; apply IH; apply closedb_inc; apply Hclosedb; omega

lemma subst_open₀_comm : ∀ x y e v, x ≠ y -> lc v -> subst x v (open₀ y e) = open₀ y (subst x v e) := by
  intros x y e v; apply subst_opening_comm

@[simp]
def maping𝕔 (e : Expr) (i : ℕ) : Expr :=
  match e with
  | .bvar j => if j == i then (.code (.bvar i)) else .bvar j
  | .fvar x => .fvar x
  | .lam₁ τ e => .lam₁ τ (maping𝕔 e (i + 1))
  | .lam₂ τ e => .lam₂ τ (maping𝕔 e (i + 1))
  | .app₁ f arg => .app₁ (maping𝕔 f i) (maping𝕔 arg i)
  | .app₂ f arg => .app₂ (maping𝕔 f i) (maping𝕔 arg i)
  | .lit₁ n => .lit₁ n
  | .lit₂ n => .lit₂ n
  | .plus₁ l r => .plus₁ (maping𝕔 l i) (maping𝕔 r i)
  | .plus₂ l r => .plus₂ (maping𝕔 l i) (maping𝕔 r i)
  | .code e => .code (maping𝕔 e i)
  | .reflect e => .reflect (maping𝕔 e i)
  | .lam𝕔 τ e => .lam𝕔 τ (maping𝕔 e (i + 1))
  | .lets b e => .lets (maping𝕔 b i) (maping𝕔 e (i + 1))
  | .let𝕔 b e => .let𝕔 (maping𝕔 b i) (maping𝕔 e (i + 1))

inductive value : Expr -> Prop where
  | lam₁ : ∀ e, lc (.lam₁ _ e) -> value (.lam₁ _ e)
  | lit₁ : ∀ n, value (.lit₁ n)
  | code : ∀ e, lc e -> value (.code e)

theorem value_lc : ∀ e, value e -> lc e := by
  intro e Hvalue
  cases Hvalue with
  | lam₁ _ Hclose => apply Hclose
  | lit₁ => constructor
  | code _ Hclose => apply Hclose

@[simp]
def map𝕔₀ (e : Expr) : Expr :=
  maping𝕔 e 0

example : map𝕔₀ (.app₁ (.bvar 0) (.lam₁ .nat (.bvar 1))) = .app₁ (.code (.bvar 0)) (.lam₁ .nat (.code (.bvar 1))) := by simp

theorem maping𝕔_intro :
    ∀ x e i, closed_at e x -> closing i x (subst x (.code (.fvar x)) (opening i (.fvar x) e)) = maping𝕔 e i :=
  by
  intros x e i Hclosed
  induction e generalizing i with
  | bvar j => by_cases HEq : j = i; rw [HEq]; simp; simp [if_neg HEq]
  | fvar y => simp at *; by_cases HEq : x = y; omega; rw [if_neg HEq]; simp; apply HEq
  | lam₁ _ _ ih
  | lam₂ _ _ ih
  | code _ ih
  | reflect _ ih
  | lam𝕔 _ _ ih =>
    simp at *; apply ih; apply Hclosed
  | app₁ _ _ ih1 ih2
  | app₂ _ _ ih1 ih2
  | plus₁ _ _ ih1 ih2
  | plus₂ _ _ ih1 ih2
  | lets _ _ ih1 ih2
  | let𝕔 _ _ ih1 ih2 =>
    simp at *; constructor; apply ih1; apply Hclosed.left; apply ih2; apply Hclosed.right
  | lit₁ => simp
  | lit₂ => simp

theorem map𝕔₀_intro : ∀ x e, closed_at e x -> close₀ x (subst x (.code (.fvar x)) (open₀ x e)) = map𝕔₀ e :=
  by
  intro _ _ Hclose
  apply maping𝕔_intro
  apply Hclose

@[simp]
def shiftl_at (x : ℕ) (n : ℕ) : Expr -> Expr
  | .bvar i => .bvar i
  | .fvar y => if x <= y then .fvar (y + n) else .fvar y
  | .lam₁ τ e => .lam₁ τ (shiftl_at x n e)
  | .lam₂ τ e => .lam₂ τ (shiftl_at x n e)
  | .app₁ f arg => .app₁ (shiftl_at x n f) (shiftl_at x n arg)
  | .app₂ f arg => .app₂ (shiftl_at x n f) (shiftl_at x n arg)
  | .lit₁ n => .lit₁ n
  | .lit₂ n => .lit₂ n
  | .plus₁ l r => .plus₁ (shiftl_at x n l) (shiftl_at x n r)
  | .plus₂ l r => .plus₂ (shiftl_at x n l) (shiftl_at x n r)
  | .code e => .code (shiftl_at x n e)
  | .reflect e => .reflect (shiftl_at x n e)
  | .lam𝕔 τ e => .lam𝕔 τ (shiftl_at x n e)
  | .lets b e => .lets (shiftl_at x n b) (shiftl_at x n e)
  | .let𝕔 b e => .let𝕔 (shiftl_at x n b) (shiftl_at x n e)

theorem shiftl_opening :
    ∀ x y e n i, x <= y -> shiftl_at x n (opening i (.fvar y) e) = opening i (.fvar (y + n)) (shiftl_at x n e) :=
  by
  intros x y e n i HLe
  induction e generalizing i with
  | bvar j =>
    by_cases HEq : j = i
    . rw [HEq]; simp; omega
    . simp; rw [if_neg HEq]; rw [if_neg HEq]; rfl
  | fvar z =>
    by_cases HLe : x <= z
    . simp; rw [if_pos HLe]; rfl
    . simp; rw [if_neg HLe]; rfl
  | app₁ _ _ IH₀ IH₁
  | app₂ _ _ IH₀ IH₁
  | plus₁ _ _ IH₀ IH₁
  | plus₂ _ _ IH₀ IH₁
  | lets _ _ IH₀ IH₁
  | let𝕔 _ _ IH₀ IH₁ =>
    simp; constructor; apply IH₀; apply IH₁
  | lit₁| lit₂ => simp
  | lam₁ _ _ IH
  | lam₂ _ _ IH
  | lam𝕔 _ _ IH
  | code _ IH
  | reflect _ IH =>
    simp; apply IH

theorem shiftl_open₀ : ∀ x y e n, x <= y -> shiftl_at x n (open₀ y e) = open₀ (y + n) (shiftl_at x n e) := by
  intros _ _ _ _; apply shiftl_opening

theorem shiftl_closed_at :
    ∀ x y e n, closed_at e x -> closed_at (shiftl_at y n e) (x + n) :=
  by
  intros x y e n Hclose
  induction e with
  | bvar j => simp
  | fvar z =>
    by_cases HLe : y <= z
    . simp; rw [if_pos HLe]; simp; apply Hclose
    . simp; rw [if_neg HLe]; simp at *; omega
  | app₁ _ _ IH₀ IH₁
  | app₂ _ _ IH₀ IH₁
  | plus₁ _ _ IH₀ IH₁
  | plus₂ _ _ IH₀ IH₁
  | lets _ _ IH₀ IH₁
  | let𝕔 _ _ IH₀ IH₁ =>
    simp; constructor
    apply IH₀; apply Hclose.left
    apply IH₁; apply Hclose.right
  | lit₁| lit₂ => simp
  | lam₁ _ _ IH
  | lam₂ _ _ IH
  | lam𝕔 _ _ IH
  | code _ IH
  | reflect _ IH =>
    simp; apply IH; apply Hclose

theorem shiftl_id :
    ∀ x e n, closed_at e x -> shiftl_at x n e = e :=
  by
  intros x e n
  induction e with
  | bvar j => simp
  | fvar y => simp; omega
  | app₁ _ _ IH₀ IH₁
  | app₂ _ _ IH₀ IH₁
  | plus₁ _ _ IH₀ IH₁
  | plus₂ _ _ IH₀ IH₁
  | lets _ _ IH₀ IH₁
  | let𝕔 _ _ IH₀ IH₁ =>
    intro Hclose; simp; constructor
    apply IH₀; apply Hclose.left
    apply IH₁; apply Hclose.right
  | lit₁| lit₂ => simp
  | lam₁ _ _ IH
  | lam₂ _ _ IH
  | lam𝕔 _ _ IH
  | code _ IH
  | reflect _ IH =>
    simp; apply IH

@[simp]
def shiftr_at (x : ℕ) : Expr -> Expr
  | .bvar i => .bvar i
  | .fvar y => if x < y then .fvar (y - 1) else .fvar y
  | .lam₁ τ e => .lam₁ τ (shiftr_at x e)
  | .lam₂ τ e => .lam₂ τ (shiftr_at x e)
  | .app₁ f arg => .app₁ (shiftr_at x f) (shiftr_at x arg)
  | .app₂ f arg => .app₂ (shiftr_at x f) (shiftr_at x arg)
  | .lit₁ n => .lit₁ n
  | .lit₂ n => .lit₂ n
  | .plus₁ l r => .plus₁ (shiftr_at x l) (shiftr_at x r)
  | .plus₂ l r => .plus₂ (shiftr_at x l) (shiftr_at x r)
  | .code e => .code (shiftr_at x e)
  | .reflect e => .reflect (shiftr_at x e)
  | .lam𝕔 τ e => .lam𝕔 τ (shiftr_at x e)
  | .lets b e => .lets (shiftr_at x b) (shiftr_at x e)
  | .let𝕔 b e => .let𝕔 (shiftr_at x b) (shiftr_at x e)

theorem shiftr_opening :
    ∀ x y e i, x < y -> shiftr_at x (opening i (.fvar y) e) = opening i (.fvar (y - 1)) (shiftr_at x e) :=
  by
  intros x y e i HLe
  induction e generalizing i with
  | bvar j =>
    by_cases HEq : j = i
    . rw [HEq]; simp; omega
    . simp; rw [if_neg HEq, if_neg HEq]; simp
  | fvar z =>
    by_cases HLe : x < z
    . simp; rw [if_pos HLe]; rfl
    . simp; rw [if_neg HLe]; rfl
  | app₁ _ _ IH₀ IH₁
  | app₂ _ _ IH₀ IH₁
  | plus₁ _ _ IH₀ IH₁
  | plus₂ _ _ IH₀ IH₁
  | lets _ _ IH₀ IH₁
  | let𝕔 _ _ IH₀ IH₁ =>
    simp; constructor; apply IH₀; apply IH₁
  | lit₁| lit₂ => simp
  | lam₁ _ _ IH
  | lam₂ _ _ IH
  | lam𝕔 _ _ IH
  | code _ IH
  | reflect _ IH =>
    simp; apply IH

theorem shiftr_open₀ : ∀ x y e, x < y -> shiftr_at x (open₀ y e) = open₀ (y - 1) (shiftr_at x e) :=
  by
  intros _ _ _
  apply shiftr_opening

theorem shiftr_closed_at : ∀ x y e, y < x -> closed_at e (x + 1) -> closed_at (shiftr_at y e) x :=
  by
  intros x y e Hxy Hclose
  induction e with
  | bvar j => simp
  | fvar z =>
    by_cases Hyz : y < z
    . simp; rw [if_pos Hyz]; simp at *; omega
    . simp; rw [if_neg Hyz]; simp at *; omega
  | app₁ _ _ IH₀ IH₁
  | app₂ _ _ IH₀ IH₁
  | plus₁ _ _ IH₀ IH₁
  | plus₂ _ _ IH₀ IH₁
  | lets _ _ IH₀ IH₁
  | let𝕔 _ _ IH₀ IH₁ =>
    simp; constructor
    apply IH₀; apply Hclose.left
    apply IH₁; apply Hclose.right
  | lit₁| lit₂ => simp
  | lam₁ _ _ IH
  | lam₂ _ _ IH
  | lam𝕔 _ _ IH
  | code _ IH
  | reflect _ IH =>
    simp; apply IH; apply Hclose

theorem shiftr_closed_at_id : ∀ x e, closed_at e x -> closed_at (shiftr_at x e) x :=
  by
  intros x e Hclose
  induction e with
  | bvar j => simp
  | fvar z =>
    by_cases Hxz : x < z
    . simp; rw [if_pos Hxz]; simp at *; omega
    . simp; rw [if_neg Hxz]; simp at *; omega
  | app₁ _ _ IH₀ IH₁
  | app₂ _ _ IH₀ IH₁
  | plus₁ _ _ IH₀ IH₁
  | plus₂ _ _ IH₀ IH₁
  | lets _ _ IH₀ IH₁
  | let𝕔 _ _ IH₀ IH₁ =>
    simp; constructor
    apply IH₀; apply Hclose.left
    apply IH₁; apply Hclose.right
  | lit₁| lit₂ => simp
  | lam₁ _ _ IH
  | lam₂ _ _ IH
  | lam𝕔 _ _ IH
  | code _ IH
  | reflect _ IH =>
    simp; apply IH; apply Hclose

theorem shiftr_id :
    ∀ x e, closed_at e (x + 1) -> shiftr_at x e = e :=
  by
  intros x e
  induction e with
  | bvar j => simp
  | fvar y => simp; omega
  | app₁ _ _ IH₀ IH₁
  | app₂ _ _ IH₀ IH₁
  | plus₁ _ _ IH₀ IH₁
  | plus₂ _ _ IH₀ IH₁
  | lets _ _ IH₀ IH₁
  | let𝕔 _ _ IH₀ IH₁ =>
    intro Hclose; simp; constructor
    apply IH₀; apply Hclose.left
    apply IH₁; apply Hclose.right
  | lit₁| lit₂ => simp
  | lam₁ _ _ IH
  | lam₂ _ _ IH
  | lam𝕔 _ _ IH
  | code _ IH
  | reflect _ IH =>
    simp; apply IH
