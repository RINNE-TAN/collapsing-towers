
import CollapsingTowers.TwoLevel.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Max
@[simp]
def fv : Expr → Finset ℕ
  | .bvar _ => ∅
  | .fvar y => { y }
  | .lam₁ e => fv e
  | .lam₂ e => fv e
  | .app₁ f arg => fv f ∪ fv arg
  | .app₂ f arg => fv f ∪ fv arg
  | .lit₁ _ => ∅
  | .lit₂ _ => ∅
  | .plus₁ l r => fv l ∪ fv r
  | .plus₂ l r => fv l ∪ fv r
  | .code e => fv e
  | .reflect e => fv e
  | .lam𝕔 e => fv e
  | .lets b e => fv b ∪ fv e
  | .let𝕔 b e => fv b ∪ fv e

@[simp]
def fresh (e : Expr) : ℕ :=
  (fv e).max.elim 0 .succ

@[simp]
def subst (x : ℕ) (v : Expr) : Expr -> Expr
  | .bvar i => .bvar i
  | .fvar y => if x == y then v else .fvar y
  | .lam₁ e => .lam₁ (subst x v e)
  | .lam₂ e => .lam₂ (subst x v e)
  | .app₁ f arg => .app₁ (subst x v f) (subst x v arg)
  | .app₂ f arg => .app₂ (subst x v f) (subst x v arg)
  | .lit₁ n => .lit₁ n
  | .lit₂ n => .lit₂ n
  | .plus₁ l r => .plus₁ (subst x v l) (subst x v r)
  | .plus₂ l r => .plus₂ (subst x v l) (subst x v r)
  | .code e => .code (subst x v e)
  | .reflect e => .reflect (subst x v e)
  | .lam𝕔 e => .lam𝕔 (subst x v e)
  | .lets b e => .lets (subst x v b) (subst x v e)
  | .let𝕔 b e => .let𝕔 (subst x v b) (subst x v e)

@[simp]
def opening (i : ℕ) (x : Expr) : Expr -> Expr
  | .bvar j => if j == i then x else .bvar j
  | .fvar x => .fvar x
  | .lam₁ e => .lam₁ (opening (i + 1) x e)
  | .lam₂ e => .lam₂ (opening (i + 1) x e)
  | .app₁ f arg => .app₁ (opening i x f) (opening i x arg)
  | .app₂ f arg => .app₂ (opening i x f) (opening i x arg)
  | .lit₁ n => .lit₁ n
  | .lit₂ n => .lit₂ n
  | .plus₁ l r => .plus₁ (opening i x l) (opening i x r)
  | .plus₂ l r => .plus₂ (opening i x l) (opening i x r)
  | .code e => .code (opening i x e)
  | .reflect e => .reflect (opening i x e)
  | .lam𝕔 e => .lam𝕔 (opening (i + 1) x e)
  | .lets b e => .lets (opening i x b) (opening (i + 1) x e)
  | .let𝕔 b e => .let𝕔 (opening i x b) (opening (i + 1) x e)

@[simp]
def open₀ (i : ℕ) : Expr -> Expr :=
  opening 0 (.fvar i)

@[simp]
def open_subst (tgt : Expr) (within : Expr) :=
  opening 0 tgt within

theorem subst_intro : ∀ x e v i, x ∉ fv e -> subst x v (opening i (.fvar x) e) = opening i v e :=
  by
  intros x e v i Hclosed
  induction e generalizing i with
  | bvar j =>
    if HEq : j = i then
      rw [HEq]
      simp
    else
      simp
      repeat rw [if_neg HEq]
      rfl
  | fvar =>
    simp at *
    intro
    contradiction
  | lam₁ _ IHe =>
    simp at *
    apply IHe
    apply Hclosed
  | lam₂ _ IHe =>
    simp at *
    apply IHe
    apply Hclosed
  | app₁ _ _ IHf IHarg =>
    simp at *
    constructor
    { apply IHf
      apply Hclosed.left
    }
    { apply IHarg
      apply Hclosed.right
    }
  | app₂ _ _ IHf IHarg =>
    simp at *
    constructor
    { apply IHf
      apply Hclosed.left
    }
    { apply IHarg
      apply Hclosed.right
    }
  | lit₁ => simp
  | lit₂ => simp
  | plus₁ _ _ IHl IHr =>
    simp at *
    constructor
    { apply IHl
      apply Hclosed.left
    }
    { apply IHr
      apply Hclosed.right
    }
  | plus₂ _ _ IHl IHr =>
    simp at *
    constructor
    { apply IHl
      apply Hclosed.left
    }
    { apply IHr
      apply Hclosed.right
    }
  | code _ IHe =>
    simp at *
    apply IHe
    apply Hclosed
  | reflect _ IHe =>
    simp at *
    apply IHe
    apply Hclosed
  | lam𝕔 _ IHe =>
    simp at *
    apply IHe
    apply Hclosed
  | lets _ _ IHb IHe =>
    simp at *
    constructor
    { apply IHb
      apply Hclosed.left
    }
    { apply IHe
      apply Hclosed.right
    }
  | let𝕔 _ _ IHb IHe =>
    simp at *
    constructor
    { apply IHb
      apply Hclosed.left
    }
    { apply IHe
      apply Hclosed.right
    }

theorem openSubst_intro : ∀ x e v, x ∉ fv e -> subst x v (open₀ x e) = open_subst v e :=
  by
  intros _ _ _ Hclosed
  apply subst_intro
  apply Hclosed

@[simp]
def closing (i : ℕ) (x : ℕ) : Expr -> Expr
  | .bvar j => .bvar j
  | .fvar y => if x == y then .bvar i else .fvar y
  | .lam₁ e => .lam₁ (closing (i + 1) x e)
  | .lam₂ e => .lam₂ (closing (i + 1) x e)
  | .app₁ f arg => .app₁ (closing i x f) (closing i x arg)
  | .app₂ f arg => .app₂ (closing i x f) (closing i x arg)
  | .lit₁ n => .lit₁ n
  | .lit₂ n => .lit₂ n
  | .plus₁ l r => .plus₁ (closing i x l) (closing i x r)
  | .plus₂ l r => .plus₂ (closing i x l) (closing i x r)
  | .code e => .code (closing i x e)
  | .reflect e => .reflect (closing i x e)
  | .lam𝕔 e => .lam𝕔 (closing (i + 1) x e)
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
  | .lam₁ e => closed_at e f
  | .lam₂ e => closed_at e f
  | .app₁ e1 e2 => closed_at e1 f ∧ closed_at e2 f
  | .app₂ e1 e2 => closed_at e1 f ∧ closed_at e2 f
  | .lit₁ _ => true
  | .lit₂ _ => true
  | .plus₁ l r => closed_at l f ∧ closed_at r f
  | .plus₂ l r => closed_at l f ∧ closed_at r f
  | .code e => closed_at e f
  | .reflect e => closed_at e f
  | .lam𝕔 e => closed_at e f
  | .lets b e => closed_at b f ∧ closed_at e f
  | .let𝕔 b e => closed_at b f ∧ closed_at e f

-- closedness condition for bound variables
@[simp]
def closedb_at (e : Expr) (b : ℕ) : Prop :=
  match e with
  | .bvar x => x < b
  | .fvar _ => true
  | .lam₁ e => closedb_at e (b + 1)
  | .lam₂ e => closedb_at e (b + 1)
  | .app₁ e1 e2 => closedb_at e1 b ∧ closedb_at e2 b
  | .app₂ e1 e2 => closedb_at e1 b ∧ closedb_at e2 b
  | .lit₁ _ => true
  | .lit₂ _ => true
  | .plus₁ l r => closedb_at l b ∧ closedb_at r b
  | .plus₂ l r => closedb_at l b ∧ closedb_at r b
  | .code e => closedb_at e b
  | .reflect e => closedb_at e b
  | .lam𝕔 e => closedb_at e (b + 1)
  | .lets e1 e2 => closedb_at e1 b ∧ closedb_at e2 (b + 1)
  | .let𝕔 e1 e2 => closedb_at e1 b ∧ closedb_at e2 (b + 1)

@[simp]
def lc e := closedb_at e 0

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

lemma open_closed : ∀ t n m,
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

lemma open_closed': ∀ t n m,
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

@[simp]
def maping𝕔 (e : Expr) (i : ℕ) : Expr :=
  match e with
  | .bvar j => if j == i then (.code (.bvar i)) else .bvar j
  | .fvar x => .fvar x
  | .lam₁ e => .lam₁ (maping𝕔 e (i + 1))
  | .lam₂ e => .lam₂ (maping𝕔 e (i + 1))
  | .app₁ f arg => .app₁ (maping𝕔 f i) (maping𝕔 arg i)
  | .app₂ f arg => .app₂ (maping𝕔 f i) (maping𝕔 arg i)
  | .lit₁ n => .lit₁ n
  | .lit₂ n => .lit₂ n
  | .plus₁ l r => .plus₁ (maping𝕔 l i) (maping𝕔 r i)
  | .plus₂ l r => .plus₂ (maping𝕔 l i) (maping𝕔 r i)
  | .code e => .code (maping𝕔 e i)
  | .reflect e => .reflect (maping𝕔 e i)
  | .lam𝕔 e => .lam𝕔 (maping𝕔 e (i + 1))
  | .lets b e => .lets (maping𝕔 b i) (maping𝕔 e (i + 1))
  | .let𝕔 b e => .let𝕔 (maping𝕔 b i) (maping𝕔 e (i + 1))

@[simp]
def map𝕔₀ (e : Expr) : Expr :=
  maping𝕔 e 0

inductive value : Expr -> Prop where
  | lam : ∀ e, closedb_at (.lam₁ e) 0 -> value (.lam₁ e)
  | lit : ∀ n, value (.lit₁ n)
  | code : ∀ e, closedb_at e 0 -> value (.code e)

example : map𝕔₀ (.app₁ (.bvar 0) (.lam₁ (.bvar 1))) = .app₁ (.code (.bvar 0)) (.lam₁ (.code (.bvar 1))) := by simp

theorem maping𝕔_intro :
    ∀ x e i, x ∉ fv e -> closing i x (subst x (.code (.fvar x)) (opening i (.fvar x) e)) = maping𝕔 e i :=
  by
  intros x e i Hclosed
  induction e generalizing i with
  | bvar j => by_cases HEq : j = i; rw [HEq]; simp; simp [if_neg HEq]
  | fvar => simp at *; repeat rw [if_neg Hclosed]; simp; apply Hclosed
  | lam₁ _ ih
  | lam₂ _ ih
  | code _ ih
  | reflect _ ih
  | lam𝕔 _ ih =>
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

theorem map𝕔₀_intro : ∀ x e, x ∉ fv e -> close₀ x (subst x (.code (.fvar x)) (open₀ x e)) = map𝕔₀ e :=
  by
  intro _ _ Hclose
  apply maping𝕔_intro
  apply Hclose
