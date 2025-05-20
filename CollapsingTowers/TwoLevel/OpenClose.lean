
import CollapsingTowers.TwoLevel.Basic
@[simp]
def subst (x : ℕ) (v : Expr) : Expr -> Expr
  | .bvar i => .bvar i
  | .fvar y => if x = y then v else .fvar y
  | .lam₁ e => .lam₁ (subst x v e)
  | .lam₂ e => .lam₂ (subst x v e)
  | .app₁ f arg => .app₁ (subst x v f) (subst x v arg)
  | .app₂ f arg => .app₂ (subst x v f) (subst x v arg)
  | .lit₁ n => .lit₁ n
  | .lit₂ n => .lit₂ (subst x v n)
  | .plus₁ l r => .plus₁ (subst x v l) (subst x v r)
  | .plus₂ l r => .plus₂ (subst x v l) (subst x v r)
  | .code e => .code (subst x v e)
  | .reflect e => .reflect (subst x v e)
  | .lam𝕔 e => .lam𝕔 (subst x v e)
  | .lets b e => .lets (subst x v b) (subst x v e)
  | .let𝕔 b e => .let𝕔 (subst x v b) (subst x v e)
  | .loc n => .loc n
  | .load₁ e => .load₁ (subst x v e)

-- opening i t1 t2 = [i -> t1]t2
@[simp]
def opening (i : ℕ) (x : Expr) : Expr -> Expr
  | .bvar j => if j = i then x else .bvar j
  | .fvar x => .fvar x
  | .lam₁ e => .lam₁ (opening (i + 1) x e)
  | .lam₂ e => .lam₂ (opening i x e)
  | .app₁ f arg => .app₁ (opening i x f) (opening i x arg)
  | .app₂ f arg => .app₂ (opening i x f) (opening i x arg)
  | .lit₁ n => .lit₁ n
  | .lit₂ n => .lit₂ (opening i x n)
  | .plus₁ l r => .plus₁ (opening i x l) (opening i x r)
  | .plus₂ l r => .plus₂ (opening i x l) (opening i x r)
  | .code e => .code (opening i x e)
  | .reflect e => .reflect (opening i x e)
  | .lam𝕔 e => .lam𝕔 (opening (i + 1) x e)
  | .lets b e => .lets (opening i x b) (opening (i + 1) x e)
  | .let𝕔 b e => .let𝕔 (opening i x b) (opening (i + 1) x e)
  | .loc n => .loc n
  | .load₁ e => .load₁ (opening i x e)

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
  | .lam₁ e => .lam₁ (closing (i + 1) x e)
  | .lam₂ e => .lam₂ (closing i x e)
  | .app₁ f arg => .app₁ (closing i x f) (closing i x arg)
  | .app₂ f arg => .app₂ (closing i x f) (closing i x arg)
  | .lit₁ n => .lit₁ n
  | .lit₂ n => .lit₂ (closing i x n)
  | .plus₁ l r => .plus₁ (closing i x l) (closing i x r)
  | .plus₂ l r => .plus₂ (closing i x l) (closing i x r)
  | .code e => .code (closing i x e)
  | .reflect e => .reflect (closing i x e)
  | .lam𝕔 e => .lam𝕔 (closing (i + 1) x e)
  | .lets b e => .lets (closing i x b) (closing (i + 1) x e)
  | .let𝕔 b e => .let𝕔 (closing i x b) (closing (i + 1) x e)
  | .loc n => .loc n
  | .load₁ e => .load₁ (closing i x e)

@[simp]
def close₀ : ℕ -> Expr -> Expr :=
  closing 0

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
  | .lit₁ _| .loc _ => true
  | .lit₂ n => closed_at n f
  | .plus₁ l r => closed_at l f ∧ closed_at r f
  | .plus₂ l r => closed_at l f ∧ closed_at r f
  | .code e => closed_at e f
  | .reflect e => closed_at e f
  | .lam𝕔 e => closed_at e f
  | .lets b e => closed_at b f ∧ closed_at e f
  | .let𝕔 b e => closed_at b f ∧ closed_at e f
  | .load₁ e => closed_at e f

-- closedness condition for bound variables
@[simp]
def closedb_at (e : Expr) (b : ℕ) : Prop :=
  match e with
  | .bvar x => x < b
  | .fvar _ => true
  | .lam₁ e => closedb_at e (b + 1)
  | .lam₂ e => closedb_at e b
  | .app₁ e1 e2 => closedb_at e1 b ∧ closedb_at e2 b
  | .app₂ e1 e2 => closedb_at e1 b ∧ closedb_at e2 b
  | .lit₁ _| .loc _ => true
  | .lit₂ n => closedb_at n b
  | .plus₁ l r => closedb_at l b ∧ closedb_at r b
  | .plus₂ l r => closedb_at l b ∧ closedb_at r b
  | .code e => closedb_at e b
  | .reflect e => closedb_at e b
  | .lam𝕔 e => closedb_at e (b + 1)
  | .lets e1 e2 => closedb_at e1 b ∧ closedb_at e2 (b + 1)
  | .let𝕔 e1 e2 => closedb_at e1 b ∧ closedb_at e2 (b + 1)
  | .load₁ e => closedb_at e b

@[simp]
def lc e := closedb_at e 0

lemma subst_intro : ∀ x e v i, closed_at e x -> subst x v (opening i (.fvar x) e) = opening i v e :=
  by
  intros _ e _ i Hclosed
  induction e generalizing i with
  | bvar j =>
    by_cases HEq : j = i
    . simp [HEq]
    . simp [if_neg HEq]
  | fvar y =>
    simp at *; omega
  | lam₁ _ IHe
  | lam₂ _ IHe
  | code _ IHe
  | reflect _ IHe
  | lam𝕔 _ IHe
  | lit₂ _ IHe
  | load₁ _ IHe =>
    simp; apply IHe; apply Hclosed
  | app₁ _ _ IH₀ IH₁
  | app₂ _ _ IH₀ IH₁
  | plus₁ _ _ IH₀ IH₁
  | plus₂ _ _ IH₀ IH₁
  | lets _ _ IH₀ IH₁
  | let𝕔 _ _ IH₀ IH₁ =>
    simp; constructor
    apply IH₀; apply Hclosed.left
    apply IH₁; apply Hclosed.right
  | lit₁| loc => simp

lemma subst_closed_id : ∀ x e v, closed_at e x -> subst x v e = e :=
  by
  intros x e v He
  induction e with
  | bvar => simp
  | fvar => simp at *; omega
  | lam₁ _ IH
  | lam₂ _ IH
  | lam𝕔 _ IH
  | code _ IH
  | reflect _ IH
  | lit₂ _ IH
  | load₁ _ IH =>
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
  | lit₁| loc => simp

lemma openSubst_intro : ∀ x e v, closed_at e x -> subst x v (open₀ x e) = open_subst v e :=
  by
  intros _ _ _ Hclosed
  apply subst_intro
  apply Hclosed

lemma closedb_inc: ∀ t i j,
    closedb_at t i -> i <= j ->
    closedb_at t j := by
  intros t i j Hclose HLe
  induction t generalizing i j with
  | bvar => simp at *; omega
  | fvar => simp
  | lam₁ _ IH
  | lam₂ _ IH
  | lam𝕔 _ IH
  | code _ IH
  | reflect _ IH
  | lit₂ _ IH
  | load₁ _ IH =>
    apply IH; apply Hclose; omega
  | app₁ _ _ IH₀ IH₁
  | app₂ _ _ IH₀ IH₁
  | plus₁ _ _ IH₀ IH₁
  | plus₂ _ _ IH₀ IH₁
  | lets _ _ IH₀ IH₁
  | let𝕔 _ _ IH₀ IH₁ =>
    apply And.intro
    . apply IH₀; apply Hclose.left; omega
    . apply IH₁; apply Hclose.right; omega
  | lit₁| loc => simp

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
  | lit₁| loc => simp
  | lam₁ _ IH
  | lam₂ _ IH
  | lam𝕔 _ IH
  | code _ IH
  | reflect _ IH
  | lit₂ _ IH
  | load₁ _ IH =>
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
  | lam₁ _ IH
  | lam₂ _ IH
  | lam𝕔 _ IH =>
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
  | reflect _ IH
  | lit₂ _ IH
  | load₁ _ IH =>
    simp; apply IH; apply Hv; apply He
  | lit₁| loc => simp

lemma subst_closed_at : ∀ x e v y, closed_at v y -> closed_at e y -> closed_at (subst x v e) y :=
  by
  intros x e v y Hv He
  induction e generalizing y with
  | bvar => apply He
  | fvar z =>
    by_cases HEq : x = z
    . rw [HEq]; simp; apply Hv
    . simp; rw [if_neg HEq]; apply He
  | lam₁ _ IH
  | lam₂ _ IH
  | lam𝕔 _ IH =>
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
  | reflect _ IH
  | lit₂ _ IH
  | load₁ _ IH =>
    simp; apply IH; apply Hv; apply He
  | lit₁| loc => simp

lemma subst_closed_at_dec : ∀ x e v, closed_at v x -> closed_at e (x + 1) -> closed_at (subst x v e) x :=
  by
  intros x e v Hv He
  induction e with
  | bvar => apply He
  | fvar z =>
    by_cases HEq : x = z
    . rw [← HEq]; simp; apply Hv
    . simp; rw [if_neg HEq]; simp at *; omega
  | lam₁ _ IH
  | lam₂ _ IH
  | lam𝕔 _ IH =>
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
  | reflect _ IH
  | lit₂ _ IH
  | load₁ _ IH =>
    simp; apply IH; apply He
  | lit₁| loc => simp

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
  case lam₁ t ih =>
    apply ih n (m + 1); simp at h; assumption
  case code _ ih
     | reflect _ ih
     | lam𝕔 _ ih
     | lit₂ _ ih
     | lam₂ t ih
     | load₁ _ ih =>
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
  case lam₁ t ih =>
    apply ih n (m + 1); simp at h; assumption
  case code _ ih
     | reflect _ ih
     | lam𝕔 _ ih
     | lit₂ _ ih
     | lam₂ t ih
     | load₁ _ ih =>
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
  | lam₁ _ IH
  | lam₂ _ IH
  | lam𝕔 _ IH
  | code _ IH
  | reflect _ IH
  | lit₂ _ IH
  | load₁ _ IH =>
    apply IH
  | app₁ _ _ IH₀ IH₁
  | app₂ _ _ IH₀ IH₁
  | plus₁ _ _ IH₀ IH₁
  | plus₂ _ _ IH₀ IH₁
  | lets _ _ IH₀ IH₁
  | let𝕔 _ _ IH₀ IH₁ =>
    intro Hclose; constructor
    apply IH₀; apply Hclose.left
    apply IH₁; apply Hclose.right
  | lit₁| loc => simp

theorem open_subst_closed : ∀ x e v i, closed_at e x -> closed_at v x -> closed_at (opening i v e) x :=
  by
  intros x e v i He Hv
  induction e generalizing i with
  | bvar j =>
    simp; by_cases HEq : j = i
    . rw [if_pos HEq]; apply Hv
    . rw [if_neg HEq]; simp
  | fvar => apply He
  | lit₁| loc => simp
  | lam₁ _ IH
  | lam₂ _ IH
  | lit₂ _ IH
  | lam𝕔 _ IH
  | code _ IH
  | reflect _ IH
  | load₁ _ IH =>
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

theorem open_closed : ∀ e x i, closed_at e x → closed_at (opening i (.fvar x) e) (x + 1) :=
  by
  intros e x i
  induction e generalizing i with
  | fvar y => simp; omega
  | bvar j =>
    by_cases HEq : j = i
    . rw [HEq]; simp
    . simp; rw [if_neg HEq]; simp
  | lam₁ _ IH
  | lam₂ _ IH
  | lam𝕔 _ IH
  | code _ IH
  | reflect _ IH
  | lit₂ _ IH
  | load₁ _ IH =>
    apply IH
  | app₁ _ _ IH₀ IH₁
  | app₂ _ _ IH₀ IH₁
  | plus₁ _ _ IH₀ IH₁
  | plus₂ _ _ IH₀ IH₁
  | lets _ _ IH₀ IH₁
  | let𝕔 _ _ IH₀ IH₁ =>
    intro Hclose; constructor
    apply IH₀; apply Hclose.left
    apply IH₁; apply Hclose.right
  | lit₁| loc => simp

theorem close_closedb : ∀ e x i j, j < i -> closedb_at e i → closedb_at (closing j x e) i :=
  by
  intros e x i j Hlt
  induction e generalizing i j with
  | fvar y =>
    by_cases HEq : x = y
    . rw [HEq]; simp; omega
    . simp; rw [if_neg HEq]; simp
  | bvar => simp
  | lam₁ _ IH
  | lam₂ _ IH
  | lam𝕔 _ IH
  | code _ IH
  | reflect _ IH
  | lit₂ _ IH
  | load₁ _ IH =>
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
  | lit₁| loc => simp

lemma closedb_opening_id: ∀ t1 t2 n,
  closedb_at t1 n -> opening n t2 t1 = t1 := by
  intros t1; induction t1 <;> intros t2 n h <;> simp
  case bvar x => intro xn; simp at h; omega
  case lam₁ t ih
     | lam₂ t ih =>
    simp at h; apply ih; assumption
  case code _ ih
     | reflect _ ih
     | lam𝕔 _ ih
     | lit₂ _ ih
     | load₁ _ ih =>
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
  | lam₁ _ IHe
  | lam₂ _ IHe
  | lam𝕔 _ IHe
  | code _ IHe
  | reflect _ IHe
  | lit₂ _ IHe
  | load₁ _ IHe =>
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
  | lit₁| loc => rfl

lemma open_close_id₀ : ∀ e x, lc e -> open₀ x (close₀ x e) = e := by apply open_close_id

lemma close_open_id : ∀ i e x, closed_at e x -> closing i x (opening i (.fvar x) e) = e :=
  by
  intros i e x Hclose
  induction e generalizing i with
  | bvar j =>
    by_cases HEq : j = i
    . simp; rw [if_pos HEq]; simp; omega
    . simp; rw [if_neg HEq]; simp
  | fvar y => simp at *; omega
  | lam₁ _ IHe
  | lam₂ _ IHe
  | lam𝕔 _ IHe
  | code _ IHe
  | reflect _ IHe
  | lit₂ _ IHe
  | load₁ _ IHe =>
    simp; apply IHe; apply Hclose
  | app₁ _ _ IH₀ IH₁
  | app₂ _ _ IH₀ IH₁
  | plus₁ _ _ IH₀ IH₁
  | plus₂ _ _ IH₀ IH₁
  | lets _ _ IH₀ IH₁
  | let𝕔 _ _ IH₀ IH₁ =>
    simp; constructor
    apply IH₀; apply Hclose.left
    apply IH₁; apply Hclose.right
  | lit₁| loc => rfl

lemma close_open_id₀ : ∀ e x, closed_at e x -> close₀ x (open₀ x e) = e := by apply close_open_id

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
  | reflect _ IH
  | lit₂ _ IH
  | load₁ _ IH =>
    simp; apply IH; apply Hclosedb
  | lit₁| loc => simp
  | lam₁ _ IH
  | lam₂ _ IH
  | lam𝕔 _ IH =>
    simp; apply IH; apply closedb_inc; apply Hclosedb; omega

lemma subst_open₀_comm : ∀ x y e v, x ≠ y -> lc v -> subst x v (open₀ y e) = open₀ y (subst x v e) := by
  intros x y e v; apply subst_opening_comm

@[simp]
def maping𝕔 (e : Expr) (i : ℕ) : Expr :=
  match e with
  | .bvar j => if j == i then (.code (.bvar i)) else .bvar j
  | .fvar x => .fvar x
  | .lam₁ e => .lam₁ (maping𝕔 e (i + 1))
  | .lam₂ e => .lam₂ (maping𝕔 e i)
  | .app₁ f arg => .app₁ (maping𝕔 f i) (maping𝕔 arg i)
  | .app₂ f arg => .app₂ (maping𝕔 f i) (maping𝕔 arg i)
  | .lit₁ n => .lit₁ n
  | .lit₂ n => .lit₂ (maping𝕔 n i)
  | .plus₁ l r => .plus₁ (maping𝕔 l i) (maping𝕔 r i)
  | .plus₂ l r => .plus₂ (maping𝕔 l i) (maping𝕔 r i)
  | .code e => .code (maping𝕔 e i)
  | .reflect e => .reflect (maping𝕔 e i)
  | .lam𝕔 e => .lam𝕔 (maping𝕔 e (i + 1))
  | .lets b e => .lets (maping𝕔 b i) (maping𝕔 e (i + 1))
  | .let𝕔 b e => .let𝕔 (maping𝕔 b i) (maping𝕔 e (i + 1))
  | .loc n => .loc n
  | .load₁ e => .load₁ (maping𝕔 e i)

inductive value : Expr -> Prop where
  | lam₁ : ∀ e, lc (.lam₁ e) -> value (.lam₁ e)
  | lit₁ : ∀ n, value (.lit₁ n)
  | code : ∀ e, lc e -> value (.code e)
  | loc : ∀ n, value (.loc n)

theorem value_lc : ∀ e, value e -> lc e := by
  intro e Hvalue
  cases Hvalue with
  | lam₁ _ Hclose => apply Hclose
  | lit₁ => constructor
  | code _ Hclose => apply Hclose
  | loc => constructor

@[simp]
def map𝕔₀ (e : Expr) : Expr :=
  maping𝕔 e 0

example : map𝕔₀ (.app₁ (.bvar 0) (.lam₁ (.bvar 1))) = .app₁ (.code (.bvar 0)) (.lam₁ (.code (.bvar 1))) := by simp

theorem maping𝕔_intro :
    ∀ x e i, closed_at e x -> closing i x (subst x (.code (.fvar x)) (opening i (.fvar x) e)) = maping𝕔 e i :=
  by
  intros x e i Hclosed
  induction e generalizing i with
  | bvar j => by_cases HEq : j = i; rw [HEq]; simp; simp [if_neg HEq]
  | fvar y => simp at *; by_cases HEq : x = y; omega; rw [if_neg HEq]; simp; apply HEq
  | lam₁ _ ih
  | lam₂ _ ih
  | code _ ih
  | reflect _ ih
  | lam𝕔 _ ih
  | lit₂ _ ih
  | load₁ _ ih =>
    simp at *; apply ih; apply Hclosed
  | app₁ _ _ ih1 ih2
  | app₂ _ _ ih1 ih2
  | plus₁ _ _ ih1 ih2
  | plus₂ _ _ ih1 ih2
  | lets _ _ ih1 ih2
  | let𝕔 _ _ ih1 ih2 =>
    simp at *; constructor; apply ih1; apply Hclosed.left; apply ih2; apply Hclosed.right
  | lit₁| loc => simp

theorem map𝕔₀_intro : ∀ x e, closed_at e x -> close₀ x (subst x (.code (.fvar x)) (open₀ x e)) = map𝕔₀ e :=
  by
  intro _ _ Hclose
  apply maping𝕔_intro
  apply Hclose

theorem maping𝕔_closed : ∀ x e i, closed_at e x -> closed_at (maping𝕔 e i) x :=
  by
  intros x e i He
  induction e generalizing i with
  | bvar j =>
    simp; by_cases HEq : j = i
    . rw [if_pos HEq]; apply He
    . rw [if_neg HEq]; simp
  | fvar => apply He
  | lit₁| loc => simp
  | lam₁ _ IH
  | lam₂ _ IH
  | lit₂ _ IH
  | lam𝕔 _ IH
  | code _ IH
  | reflect _ IH
  | load₁ _ IH =>
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

@[simp]
def swapdb (i : ℕ) (j : ℕ) : Expr -> Expr
  | .bvar k => if k = i then .bvar j else if k = j then .bvar i else .bvar k
  | .fvar x => .fvar x
  | .lam₁ e => .lam₁ (swapdb (i + 1) (j + 1) e)
  | .lam₂ e => .lam₂ (swapdb i j e)
  | .app₁ f arg => .app₁ (swapdb i j f) (swapdb i j arg)
  | .app₂ f arg => .app₂ (swapdb i j f) (swapdb i j arg)
  | .lit₁ n => .lit₁ n
  | .lit₂ n => .lit₂ (swapdb i j n)
  | .plus₁ l r => .plus₁ (swapdb i j l) (swapdb i j r)
  | .plus₂ l r => .plus₂ (swapdb i j l) (swapdb i j r)
  | .code e => .code (swapdb i j e)
  | .reflect e => .reflect (swapdb i j e)
  | .lam𝕔 e => .lam𝕔 (swapdb (i + 1) (j + 1) e)
  | .lets b e => .lets (swapdb i j b) (swapdb (i + 1) (j + 1) e)
  | .let𝕔 b e => .let𝕔 (swapdb i j b) (swapdb (i + 1) (j + 1) e)
  | .loc n => .loc n
  | .load₁ e => .load₁ (swapdb i j e)

theorem swapdb_closed : ∀ x e i j, closed_at e x -> closed_at (swapdb i j e) x :=
  by
  intros x e i j Hclose
  induction e generalizing i j with
  | bvar k =>
    simp; by_cases HEq : k = i
    . rw [if_pos HEq]; apply Hclose
    . rw [if_neg HEq]
      by_cases HEq : k = j
      . rw [if_pos HEq]; apply Hclose
      . rw [if_neg HEq]; simp
  | fvar => apply Hclose
  | lit₁| loc => simp
  | lam₁ _ IH
  | lam₂ _ IH
  | lit₂ _ IH
  | lam𝕔 _ IH
  | code _ IH
  | reflect _ IH
  | load₁ _ IH =>
    apply IH; apply Hclose
  | app₁ _ _ IH₀ IH₁
  | app₂ _ _ IH₀ IH₁
  | plus₁ _ _ IH₀ IH₁
  | plus₂ _ _ IH₀ IH₁
  | lets _ _ IH₀ IH₁
  | let𝕔 _ _ IH₀ IH₁ =>
    constructor
    apply IH₀; apply Hclose.left
    apply IH₁; apply Hclose.right

@[simp]
def swap (x : ℕ) (y : ℕ) : Expr -> Expr
  | .bvar k => .bvar k
  | .fvar z => if z = x then .fvar y else if z = y then .fvar x else .fvar z
  | .lam₁ e => .lam₁ (swap x y e)
  | .lam₂ e => .lam₂ (swap x y e)
  | .app₁ f arg => .app₁ (swap x y f) (swap x y arg)
  | .app₂ f arg => .app₂ (swap x y f) (swap x y arg)
  | .lit₁ n => .lit₁ n
  | .lit₂ n => .lit₂ (swap x y n)
  | .plus₁ l r => .plus₁ (swap x y l) (swap x y r)
  | .plus₂ l r => .plus₂ (swap x y l) (swap x y r)
  | .code e => .code (swap x y e)
  | .reflect e => .reflect (swap x y e)
  | .lam𝕔 e => .lam𝕔 (swap x y e)
  | .lets b e => .lets (swap x y b) (swap x y e)
  | .let𝕔 b e => .let𝕔 (swap x y b) (swap x y e)
  | .loc n => .loc n
  | .load₁ e => .load₁ (swap x y e)

theorem open_swapdb_comm :
  ∀ i j x y e,
  closed_at e x ->
  closed_at e y ->
  i ≠ j ->
  opening i (.fvar x) (opening j (.fvar y) (swapdb i j e)) = swap x y (opening i (.fvar x) (opening j (.fvar y) e)) :=
  by
  intros i j x y e Hclosex Hclosey HNe
  induction e generalizing i j with
  | fvar =>
    simp
    rw [if_neg (Nat.ne_of_lt Hclosex)]
    rw [if_neg (Nat.ne_of_lt Hclosey)]
  | bvar k =>
    simp; by_cases HEqj : k = j
    . repeat rw [if_pos HEqj]
      simp; by_cases HEqi : k = i
      . omega
      . repeat rw [if_neg HEqi]
        simp; rw [if_neg HNe]
        simp; by_cases HEq : y = x
        . rw [if_pos HEq]; simp; omega
        . rw [if_neg HEq]
    . repeat rw [if_neg HEqj]
      simp; by_cases HEqi : k = i
      . repeat rw [if_pos HEqi]
        simp
      . repeat rw [if_neg HEqi]
        simp; rw [if_neg HEqj]
        simp; omega
  | lit₁| loc => simp
  | lam₁ _ IH
  | lam₂ _ IH
  | lit₂ _ IH
  | lam𝕔 _ IH
  | code _ IH
  | reflect _ IH
  | load₁ _ IH =>
    simp; apply IH
    apply Hclosex; apply Hclosey; omega
  | app₁ _ _ IH₀ IH₁
  | app₂ _ _ IH₀ IH₁
  | plus₁ _ _ IH₀ IH₁
  | plus₂ _ _ IH₀ IH₁
  | lets _ _ IH₀ IH₁
  | let𝕔 _ _ IH₀ IH₁ =>
    simp; constructor
    apply IH₀; apply Hclosex.left; apply Hclosey.left; omega
    apply IH₁; apply Hclosex.right; apply Hclosey.right; omega

theorem open_swap_comm :
  ∀ i x y z e,
  z ≠ x ->
  z ≠ y ->
  opening i (.fvar z) (swap x y e) = swap x y (opening i (.fvar z) e) :=
  by
  intros i x y z e HNex HNey
  induction e generalizing i with
  | fvar k =>
    simp; by_cases HEqx : k = x
    . rw [if_pos HEqx]; simp
    . rw [if_neg HEqx]
      by_cases HEqy : k = y
      . rw [if_pos HEqy]; simp
      . rw [if_neg HEqy]; simp
  | bvar j =>
    simp; by_cases HEq : j = i
    . rw [if_pos HEq]
      simp; rw [if_neg HNex, if_neg HNey]
    . rw [if_neg HEq]; simp
  | lit₁| loc => simp
  | lam₁ _ IH
  | lam₂ _ IH
  | lit₂ _ IH
  | lam𝕔 _ IH
  | code _ IH
  | reflect _ IH
  | load₁ _ IH =>
    simp; apply IH
  | app₁ _ _ IH₀ IH₁
  | app₂ _ _ IH₀ IH₁
  | plus₁ _ _ IH₀ IH₁
  | plus₂ _ _ IH₀ IH₁
  | lets _ _ IH₀ IH₁
  | let𝕔 _ _ IH₀ IH₁ =>
    simp; constructor
    apply IH₀; apply IH₁

theorem open₀_swap_comm :
  ∀ x y z e,
  z ≠ x ->
  z ≠ y ->
  open₀ z (swap x y e) = swap x y (open₀ z e) := by apply open_swap_comm

theorem swap_closed :
  ∀ x y z e,
  x < z ->
  y < z ->
  closed_at e z ->
  closed_at (swap x y e) z :=
  by
  intros x y z e HLex HLty Hclose
  induction e with
  | bvar => simp
  | fvar k =>
    simp; by_cases HEqx : k = x
    . rw [if_pos HEqx]; simp; omega
    . rw [if_neg HEqx]
      by_cases HEqy : k = y
      . rw [if_pos HEqy]; simp; omega
      . rw [if_neg HEqy]; apply Hclose
  | lit₁| loc => simp
  | lam₁ _ IH
  | lam₂ _ IH
  | lit₂ _ IH
  | lam𝕔 _ IH
  | code _ IH
  | reflect _ IH
  | load₁ _ IH =>
    apply IH; apply Hclose
  | app₁ _ _ IH₀ IH₁
  | app₂ _ _ IH₀ IH₁
  | plus₁ _ _ IH₀ IH₁
  | plus₂ _ _ IH₀ IH₁
  | lets _ _ IH₀ IH₁
  | let𝕔 _ _ IH₀ IH₁ =>
    constructor
    apply IH₀; apply Hclose.left
    apply IH₁; apply Hclose.right
