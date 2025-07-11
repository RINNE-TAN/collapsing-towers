
import Mathlib.Data.Set.Insert
import CollapsingTowers.TwoLevelFull.Syntax
-- Definitions
@[simp]
def subst (x : ℕ) (v : Expr) : Expr → Expr
  | .bvar i => .bvar i
  | .fvar y => if x = y then v else .fvar y
  | .lam e => .lam (subst x v e)
  | .lift e => .lift (subst x v e)
  | .app₁ f arg => .app₁ (subst x v f) (subst x v arg)
  | .app₂ f arg => .app₂ (subst x v f) (subst x v arg)
  | .lit n => .lit n
  | .unit => .unit
  | .binary₁ op l r => .binary₁ op (subst x v l) (subst x v r)
  | .binary₂ op l r => .binary₂ op (subst x v l) (subst x v r)
  | .run e => .run (subst x v e)
  | .code e => .code (subst x v e)
  | .reflect e => .reflect (subst x v e)
  | .lam𝕔 e => .lam𝕔 (subst x v e)
  | .lets b e => .lets (subst x v b) (subst x v e)
  | .let𝕔 b e => .let𝕔 (subst x v b) (subst x v e)
  | .loc l => .loc l
  | .load₁ e => .load₁ (subst x v e)
  | .alloc₁ e => .alloc₁ (subst x v e)
  | .store₁ l r => .store₁ (subst x v l) (subst x v r)
  | .load₂ e => .load₂ (subst x v e)
  | .alloc₂ e => .alloc₂ (subst x v e)
  | .store₂ l r => .store₂ (subst x v l) (subst x v r)
  | .ifz₁ c l r => .ifz₁ (subst x v c) (subst x v l) (subst x v r)
  | .ifz₂ c l r => .ifz₂ (subst x v c) (subst x v l) (subst x v r)
  | .fix₁ e => .fix₁ (subst x v e)
  | .fix₂ e => .fix₂ (subst x v e)

-- opening i t1 t2 = [i → t1]t2
@[simp]
def opening (i : ℕ) (x : Expr) : Expr → Expr
  | .bvar j => if j = i then x else .bvar j
  | .fvar x => .fvar x
  | .lam e => .lam (opening (i + 1) x e)
  | .lift e => .lift (opening i x e)
  | .app₁ f arg => .app₁ (opening i x f) (opening i x arg)
  | .app₂ f arg => .app₂ (opening i x f) (opening i x arg)
  | .lit n => .lit n
  | .unit => .unit
  | .binary₁ op l r => .binary₁ op (opening i x l) (opening i x r)
  | .binary₂ op l r => .binary₂ op (opening i x l) (opening i x r)
  | .run e => .run (opening i x e)
  | .code e => .code (opening i x e)
  | .reflect e => .reflect (opening i x e)
  | .lam𝕔 e => .lam𝕔 (opening (i + 1) x e)
  | .lets b e => .lets (opening i x b) (opening (i + 1) x e)
  | .let𝕔 b e => .let𝕔 (opening i x b) (opening (i + 1) x e)
  | .loc l => .loc l
  | .load₁ e => .load₁ (opening i x e)
  | .alloc₁ e => .alloc₁ (opening i x e)
  | .store₁ l r => .store₁ (opening i x l) (opening i x r)
  | .load₂ e => .load₂ (opening i x e)
  | .alloc₂ e => .alloc₂ (opening i x e)
  | .store₂ l r => .store₂ (opening i x l) (opening i x r)
  | .ifz₁ c l r => .ifz₁ (opening i x c)  (opening i x l) (opening i x r)
  | .ifz₂ c l r => .ifz₂ (opening i x c)  (opening i x l) (opening i x r)
  | .fix₁ e => .fix₁ (opening i x e)
  | .fix₂ e => .fix₂ (opening i x e)

@[simp]
def open₀ (x : ℕ) : Expr → Expr :=
  opening 0 (.fvar x)

@[simp]
def open_subst (tgt : Expr) (within : Expr) :=
  opening 0 tgt within

@[simp]
def closing (i : ℕ) (x : ℕ) : Expr → Expr
  | .bvar j => .bvar j
  | .fvar y => if x == y then .bvar i else .fvar y
  | .lam e => .lam (closing (i + 1) x e)
  | .lift e => .lift (closing i x e)
  | .app₁ f arg => .app₁ (closing i x f) (closing i x arg)
  | .app₂ f arg => .app₂ (closing i x f) (closing i x arg)
  | .lit n => .lit n
  | .unit => .unit
  | .binary₁ op l r => .binary₁ op (closing i x l) (closing i x r)
  | .binary₂ op l r => .binary₂ op (closing i x l) (closing i x r)
  | .run e => .run (closing i x e)
  | .code e => .code (closing i x e)
  | .reflect e => .reflect (closing i x e)
  | .lam𝕔 e => .lam𝕔 (closing (i + 1) x e)
  | .lets b e => .lets (closing i x b) (closing (i + 1) x e)
  | .let𝕔 b e => .let𝕔 (closing i x b) (closing (i + 1) x e)
  | .loc l => .loc l
  | .load₁ e => .load₁ (closing i x e)
  | .alloc₁ e => .alloc₁ (closing i x e)
  | .store₁ l r => .store₁ (closing i x l) (closing i x r)
  | .load₂ e => .load₂ (closing i x e)
  | .alloc₂ e => .alloc₂ (closing i x e)
  | .store₂ l r => .store₂ (closing i x l) (closing i x r)
  | .ifz₁ c l r => .ifz₁ (closing i x c) (closing i x l) (closing i x r)
  | .ifz₂ c l r => .ifz₂ (closing i x c) (closing i x l) (closing i x r)
  | .fix₁ e => .fix₁ (closing i x e)
  | .fix₂ e => .fix₂ (closing i x e)

@[simp]
def close₀ : ℕ → Expr → Expr :=
  closing 0

-- closedness condition for free variables
@[simp]
def closed_at (e : Expr) (f : ℕ) : Prop :=
  match e with
  | .bvar _ => true
  | .fvar x => x < f
  | .lam e => closed_at e f
  | .lift e => closed_at e f
  | .app₁ e1 e2 => closed_at e1 f ∧ closed_at e2 f
  | .app₂ e1 e2 => closed_at e1 f ∧ closed_at e2 f
  | .lit _ => true
  | .unit => true
  | .binary₁ _ l r => closed_at l f ∧ closed_at r f
  | .binary₂ _ l r => closed_at l f ∧ closed_at r f
  | .run e => closed_at e f
  | .code e => closed_at e f
  | .reflect e => closed_at e f
  | .lam𝕔 e => closed_at e f
  | .lets b e => closed_at b f ∧ closed_at e f
  | .let𝕔 b e => closed_at b f ∧ closed_at e f
  | .loc _ => true
  | .load₁ e => closed_at e f
  | .alloc₁ e => closed_at e f
  | .store₁ l r => closed_at l f ∧ closed_at r f
  | .load₂ e => closed_at e f
  | .alloc₂ e => closed_at e f
  | .store₂ l r => closed_at l f ∧ closed_at r f
  | .ifz₁ c l r => closed_at c f ∧ closed_at l f ∧ closed_at r f
  | .ifz₂ c l r => closed_at c f ∧ closed_at l f ∧ closed_at r f
  | .fix₁ e => closed_at e f
  | .fix₂ e => closed_at e f

@[simp]
def closed e := closed_at e 0

-- closedness condition for bound variables
@[simp]
def lc_at (e : Expr) (b : ℕ) : Prop :=
  match e with
  | .bvar x => x < b
  | .fvar _ => true
  | .lam e => lc_at e (b + 1)
  | .lift e => lc_at e b
  | .app₁ e1 e2 => lc_at e1 b ∧ lc_at e2 b
  | .app₂ e1 e2 => lc_at e1 b ∧ lc_at e2 b
  | .lit _ => true
  | .unit => true
  | .binary₁ _ l r => lc_at l b ∧ lc_at r b
  | .binary₂ _ l r => lc_at l b ∧ lc_at r b
  | .run e => lc_at e b
  | .code e => lc_at e b
  | .reflect e => lc_at e b
  | .lam𝕔 e => lc_at e (b + 1)
  | .lets e1 e2 => lc_at e1 b ∧ lc_at e2 (b + 1)
  | .let𝕔 e1 e2 => lc_at e1 b ∧ lc_at e2 (b + 1)
  | .loc _ => true
  | .load₁ e => lc_at e b
  | .alloc₁ e => lc_at e b
  | .store₁ l r => lc_at l b ∧ lc_at r b
  | .load₂ e => lc_at e b
  | .alloc₂ e => lc_at e b
  | .store₂ l r => lc_at l b ∧ lc_at r b
  | .ifz₁ c l r => lc_at c b ∧ lc_at l b ∧ lc_at r b
  | .ifz₂ c l r => lc_at c b ∧ lc_at l b ∧ lc_at r b
  | .fix₁ e => lc_at e b
  | .fix₂ e => lc_at e b

@[simp]
def lc e := lc_at e 0

@[simp]
def maping𝕔 (e : Expr) (i : ℕ) : Expr :=
  match e with
  | .bvar j => if j == i then (.code (.bvar i)) else .bvar j
  | .fvar x => .fvar x
  | .lam e => .lam (maping𝕔 e (i + 1))
  | .lift e => .lift (maping𝕔 e i)
  | .app₁ f arg => .app₁ (maping𝕔 f i) (maping𝕔 arg i)
  | .app₂ f arg => .app₂ (maping𝕔 f i) (maping𝕔 arg i)
  | .lit n => .lit n
  | .unit => .unit
  | .binary₁ op l r => .binary₁ op (maping𝕔 l i) (maping𝕔 r i)
  | .binary₂ op l r => .binary₂ op (maping𝕔 l i) (maping𝕔 r i)
  | .run e => .run (maping𝕔 e i)
  | .code e => .code (maping𝕔 e i)
  | .reflect e => .reflect (maping𝕔 e i)
  | .lam𝕔 e => .lam𝕔 (maping𝕔 e (i + 1))
  | .lets b e => .lets (maping𝕔 b i) (maping𝕔 e (i + 1))
  | .let𝕔 b e => .let𝕔 (maping𝕔 b i) (maping𝕔 e (i + 1))
  | .loc l => .loc l
  | .load₁ e => .load₁ (maping𝕔 e i)
  | .alloc₁ e => .alloc₁ (maping𝕔 e i)
  | .store₁ l r => .store₁ (maping𝕔 l i) (maping𝕔 r i)
  | .load₂ e => .load₂ (maping𝕔 e i)
  | .alloc₂ e => .alloc₂ (maping𝕔 e i)
  | .store₂ l r => .store₂ (maping𝕔 l i) (maping𝕔 r i)
  | .ifz₁ c l r => .ifz₁ (maping𝕔 c i) (maping𝕔 l i) (maping𝕔 r i)
  | .ifz₂ c l r => .ifz₂ (maping𝕔 c i) (maping𝕔 l i) (maping𝕔 r i)
  | .fix₁ e => .fix₁ (maping𝕔 e i)
  | .fix₂ e => .fix₂ (maping𝕔 e i)

@[simp]
def map𝕔₀ (e : Expr) : Expr := maping𝕔 e 0

@[simp]
def fv : Expr → Set ℕ
  | .bvar _ => ∅
  | .fvar x => { x }
  | .lam e => fv e
  | .lift e => fv e
  | .app₁ f arg => fv f ∪ fv arg
  | .app₂ f arg => fv f ∪ fv arg
  | .lit _ => ∅
  | .unit => ∅
  | .binary₁ _ l r => fv l ∪ fv r
  | .binary₂ _ l r => fv l ∪ fv r
  | .run e => fv e
  | .code e => fv e
  | .reflect e => fv e
  | .lam𝕔 e => fv e
  | .lets b e => fv b ∪ fv e
  | .let𝕔 b e => fv b ∪ fv e
  | .loc _ => ∅
  | .load₁ e => fv e
  | .alloc₁ e => fv e
  | .store₁ l r => fv l ∪ fv r
  | .load₂ e => fv e
  | .alloc₂ e => fv e
  | .store₂ l r => fv l ∪ fv r
  | .ifz₁ c l r => fv c ∪ fv l ∪ fv r
  | .ifz₂ c l r => fv c ∪ fv l ∪ fv r
  | .fix₁ e => fv e
  | .fix₂ e => fv e

-- Properties
lemma subst_intro : ∀ x e v i, closed_at e x → subst x v (opening i (.fvar x) e) = opening i v e :=
  by
  intros _ e _ i Hclosed
  induction e generalizing i with
  | bvar j =>
    by_cases HEq : j = i
    . simp [HEq]
    . simp [if_neg HEq]
  | fvar y =>
    simp at *; omega
  | lam _ IH
  | lift _ IH
  | code _ IH
  | reflect _ IH
  | lam𝕔 _ IH
  | run _ IH
  | load₁ _ IH
  | alloc₁ _ IH
  | load₂ _ IH
  | alloc₂ _ IH
  | fix₁ _ IH
  | fix₂ _ IH =>
    simp; apply IH; apply Hclosed
  | app₁ _ _ IH₀ IH₁
  | app₂ _ _ IH₀ IH₁
  | binary₁ _ _ _ IH₀ IH₁
  | binary₂ _ _ _ IH₀ IH₁
  | lets _ _ IH₀ IH₁
  | let𝕔 _ _ IH₀ IH₁
  | store₁ _ _ IH₀ IH₁
  | store₂ _ _ IH₀ IH₁ =>
    simp; constructor
    apply IH₀; apply Hclosed.left
    apply IH₁; apply Hclosed.right
  | lit| loc| unit => simp
  | ifz₁ _ _ _ IH₀ IH₁ IH₂
  | ifz₂ _ _ _ IH₀ IH₁ IH₂ =>
    simp; constructor
    apply IH₀; apply Hclosed.left; constructor
    apply IH₁; apply Hclosed.right.left
    apply IH₂; apply Hclosed.right.right

lemma subst_closed_id : ∀ x e v, closed_at e x → subst x v e = e :=
  by
  intros x e v He
  induction e with
  | bvar => simp
  | fvar => simp at *; omega
  | lam _ IH
  | lift _ IH
  | lam𝕔 _ IH
  | code _ IH
  | reflect _ IH
  | run _ IH
  | load₁ _ IH
  | alloc₁ _ IH
  | load₂ _ IH
  | alloc₂ _ IH
  | fix₁ _ IH
  | fix₂ _ IH =>
    simp; apply IH; apply He
  | app₁ _ _ IH₀ IH₁
  | app₂ _ _ IH₀ IH₁
  | binary₁ _ _ _ IH₀ IH₁
  | binary₂ _ _ _ IH₀ IH₁
  | store₁ _ _ IH₀ IH₁
  | store₂ _ _ IH₀ IH₁ =>
    simp; constructor
    apply IH₀; apply He.left
    apply IH₁; apply He.right
  | lets _ _ IHb IH
  | let𝕔 _ _ IHb IH =>
    simp; constructor
    apply IHb; apply He.left
    apply IH; apply He.right
  | lit| loc| unit => simp
  | ifz₁ _ _ _ IH₀ IH₁ IH₂
  | ifz₂ _ _ _ IH₀ IH₁ IH₂ =>
    simp; constructor
    apply IH₀; apply He.left; constructor
    apply IH₁; apply He.right.left
    apply IH₂; apply He.right.right

lemma openSubst_intro : ∀ x e v, closed_at e x → subst x v (open₀ x e) = open_subst v e :=
  by
  intros _ _ _ Hclosed
  apply subst_intro
  apply Hclosed

lemma lc_inc: ∀ t i j,
    lc_at t i → i ≤ j →
    lc_at t j := by
  intros t i j Hclose HLe
  induction t generalizing i j with
  | bvar => simp at *; omega
  | fvar => simp
  | lam _ IH
  | lift _ IH
  | lam𝕔 _ IH
  | code _ IH
  | reflect _ IH
  | run _ IH
  | load₁ _ IH
  | alloc₁ _ IH
  | load₂ _ IH
  | alloc₂ _ IH
  | fix₁ _ IH
  | fix₂ _ IH =>
    apply IH; apply Hclose; omega
  | app₁ _ _ IH₀ IH₁
  | app₂ _ _ IH₀ IH₁
  | binary₁ _ _ _ IH₀ IH₁
  | binary₂ _ _ _ IH₀ IH₁
  | lets _ _ IH₀ IH₁
  | let𝕔 _ _ IH₀ IH₁
  | store₁ _ _ IH₀ IH₁
  | store₂ _ _ IH₀ IH₁ =>
    apply And.intro
    . apply IH₀; apply Hclose.left; omega
    . apply IH₁; apply Hclose.right; omega
  | lit| loc| unit => simp
  | ifz₁ _ _ _ IH₀ IH₁ IH₂
  | ifz₂ _ _ _ IH₀ IH₁ IH₂ =>
    simp; constructor
    apply IH₀; apply Hclose.left; omega; constructor
    apply IH₁; apply Hclose.right.left; omega
    apply IH₂; apply Hclose.right.right; omega

lemma closed_inc : ∀ x y e, closed_at e x → x ≤ y → closed_at e y :=
  by
  intros x y e Hclose Hxy
  induction e with
  | bvar j => simp
  | fvar z => simp at *; omega
  | app₁ _ _ IH₀ IH₁
  | app₂ _ _ IH₀ IH₁
  | binary₁ _ _ _ IH₀ IH₁
  | binary₂ _ _ _ IH₀ IH₁
  | lets _ _ IH₀ IH₁
  | let𝕔 _ _ IH₀ IH₁
  | store₁ _ _ IH₀ IH₁
  | store₂ _ _ IH₀ IH₁ =>
    simp; constructor
    apply IH₀; apply Hclose.left
    apply IH₁; apply Hclose.right
  | lit| loc| unit => simp
  | lam _ IH
  | lift _ IH
  | lam𝕔 _ IH
  | code _ IH
  | reflect _ IH
  | run _ IH
  | load₁ _ IH
  | alloc₁ _ IH
  | load₂ _ IH
  | alloc₂ _ IH
  | fix₁ _ IH
  | fix₂ _ IH =>
    simp; apply IH; apply Hclose
  | ifz₁ _ _ _ IH₀ IH₁ IH₂
  | ifz₂ _ _ _ IH₀ IH₁ IH₂ =>
    simp; constructor
    apply IH₀; apply Hclose.left; constructor
    apply IH₁; apply Hclose.right.left
    apply IH₂; apply Hclose.right.right

lemma subst_lc_at : ∀ x e v i, lc_at v i → lc_at e i → lc_at (subst x v e) i :=
  by
  intros x e v i Hv He
  induction e generalizing i with
  | bvar => apply He
  | fvar y =>
    by_cases HEq : x = y
    . rw [HEq]; simp; apply Hv
    . simp; rw [if_neg HEq]; simp
  | lam _ IH
  | lift _ IH
  | lam𝕔 _ IH =>
    apply IH; apply lc_inc; apply Hv; omega; apply He
  | app₁ _ _ IH₀ IH₁
  | app₂ _ _ IH₀ IH₁
  | binary₁ _ _ _ IH₀ IH₁
  | binary₂ _ _ _ IH₀ IH₁
  | store₁ _ _ IH₀ IH₁
  | store₂ _ _ IH₀ IH₁ =>
    constructor
    apply IH₀; apply Hv; apply He.left
    apply IH₁; apply Hv; apply He.right
  | lets _ _ IHb IH
  | let𝕔 _ _ IHb IH =>
    constructor
    apply IHb; apply Hv; apply He.left
    apply IH; apply lc_inc; apply Hv; omega; apply He.right
  | code _ IH
  | reflect _ IH
  | run _ IH
  | load₁ _ IH
  | alloc₁ _ IH
  | load₂ _ IH
  | alloc₂ _ IH
  | fix₁ _ IH
  | fix₂ _ IH =>
    simp; apply IH; apply Hv; apply He
  | lit| loc| unit => simp
  | ifz₁ _ _ _ IH₀ IH₁ IH₂
  | ifz₂ _ _ _ IH₀ IH₁ IH₂ =>
    simp; constructor
    apply IH₀; apply Hv; apply He.left; constructor
    apply IH₁; apply Hv; apply He.right.left
    apply IH₂; apply Hv; apply He.right.right

lemma subst_closed_at : ∀ x e v y, closed_at v y → closed_at e y → closed_at (subst x v e) y :=
  by
  intros x e v y Hv He
  induction e generalizing y with
  | bvar => apply He
  | fvar z =>
    by_cases HEq : x = z
    . rw [HEq]; simp; apply Hv
    . simp; rw [if_neg HEq]; apply He
  | lam _ IH
  | lift _ IH
  | lam𝕔 _ IH =>
    apply IH; apply Hv; apply He
  | app₁ _ _ IH₀ IH₁
  | app₂ _ _ IH₀ IH₁
  | binary₁ _ _ _ IH₀ IH₁
  | binary₂ _ _ _ IH₀ IH₁
  | lets _ _ IH₀ IH₁
  | let𝕔 _ _ IH₀ IH₁
  | store₁ _ _ IH₀ IH₁
  | store₂ _ _ IH₀ IH₁ =>
    constructor
    apply IH₀; apply Hv; apply He.left
    apply IH₁; apply Hv; apply He.right
  | code _ IH
  | reflect _ IH
  | run _ IH
  | load₁ _ IH
  | alloc₁ _ IH
  | load₂ _ IH
  | alloc₂ _ IH
  | fix₁ _ IH
  | fix₂ _ IH =>
    simp; apply IH; apply Hv; apply He
  | lit| loc| unit => simp
  | ifz₁ _ _ _ IH₀ IH₁ IH₂
  | ifz₂ _ _ _ IH₀ IH₁ IH₂ =>
    simp; constructor
    apply IH₀; apply Hv; apply He.left; constructor
    apply IH₁; apply Hv; apply He.right.left
    apply IH₂; apply Hv; apply He.right.right

lemma subst_closed_at_dec : ∀ x e v, closed_at v x → closed_at e (x + 1) → closed_at (subst x v e) x :=
  by
  intros x e v Hv He
  induction e with
  | bvar => apply He
  | fvar z =>
    by_cases HEq : x = z
    . rw [← HEq]; simp; apply Hv
    . simp; rw [if_neg HEq]; simp at *; omega
  | lam _ IH
  | lift _ IH
  | lam𝕔 _ IH =>
    apply IH; apply He
  | app₁ _ _ IH₀ IH₁
  | app₂ _ _ IH₀ IH₁
  | binary₁ _ _ _ IH₀ IH₁
  | binary₂ _ _ _ IH₀ IH₁
  | lets _ _ IH₀ IH₁
  | let𝕔 _ _ IH₀ IH₁
  | store₁ _ _ IH₀ IH₁
  | store₂ _ _ IH₀ IH₁ =>
    constructor
    apply IH₀; apply He.left
    apply IH₁; apply He.right
  | code _ IH
  | reflect _ IH
  | run _ IH
  | load₁ _ IH
  | alloc₁ _ IH
  | load₂ _ IH
  | alloc₂ _ IH
  | fix₁ _ IH
  | fix₂ _ IH =>
    simp; apply IH; apply He
  | lit| loc| unit => simp
  | ifz₁ _ _ _ IH₀ IH₁ IH₂
  | ifz₂ _ _ _ IH₀ IH₁ IH₂ =>
    simp; constructor
    apply IH₀; apply He.left; constructor
    apply IH₁; apply He.right.left
    apply IH₂; apply He.right.right

lemma open_lc : ∀ i x e, lc_at (opening i (.fvar x) e) i ↔ lc_at e (i + 1) :=
  by
  intros i x e
  induction e generalizing i with
  | bvar j =>
    simp; by_cases HEq : j = i
    . rw [if_pos HEq]; constructor
      . omega
      . simp
    . rw [if_neg HEq]; simp; omega
  | fvar => simp
  | lit| loc| unit => simp
  | lam _ IH
  | lift _ IH
  | lam𝕔 _ IH
  | code _ IH
  | reflect _ IH
  | run _ IH
  | load₁ _ IH
  | alloc₁ _ IH
  | load₂ _ IH
  | alloc₂ _ IH
  | fix₁ _ IH
  | fix₂ _ IH =>
    apply IH
  | app₁ _ _ IH₀ IH₁
  | app₂ _ _ IH₀ IH₁
  | binary₁ _ _ _ IH₀ IH₁
  | binary₂ _ _ _ IH₀ IH₁
  | lets _ _ IH₀ IH₁
  | let𝕔 _ _ IH₀ IH₁
  | store₁ _ _ IH₀ IH₁
  | store₂ _ _ IH₀ IH₁ =>
    constructor
    . intro Hlc
      constructor
      apply (IH₀ _).mp; apply Hlc.left
      apply (IH₁ _).mp; apply Hlc.right
    . intro Hlc
      constructor
      apply (IH₀ _).mpr; apply Hlc.left
      apply (IH₁ _).mpr; apply Hlc.right
  | ifz₁ _ _ _ IH₀ IH₁ IH₂
  | ifz₂ _ _ _ IH₀ IH₁ IH₂ =>
    constructor
    . intro Hlc
      constructor
      apply (IH₀ _).mp; apply Hlc.left; constructor
      apply (IH₁ _).mp; apply Hlc.right.left
      apply (IH₂ _).mp; apply Hlc.right.right
    . intro Hlc
      constructor
      apply (IH₀ _).mpr; apply Hlc.left; constructor
      apply (IH₁ _).mpr; apply Hlc.right.left
      apply (IH₂ _).mpr; apply Hlc.right.right

lemma close_closed : ∀ e x i, closed_at e (x + 1) ↔ closed_at (closing i x e) x :=
  by
  intros e x i
  induction e generalizing i with
  | fvar y =>
    by_cases HEq : x = y
    . rw [HEq]; simp
    . simp; rw [if_neg HEq]; simp; omega
  | bvar => simp
  | lam _ IH
  | lift _ IH
  | lam𝕔 _ IH
  | code _ IH
  | reflect _ IH
  | run _ IH
  | load₁ _ IH
  | alloc₁ _ IH
  | load₂ _ IH
  | alloc₂ _ IH
  | fix₁ _ IH
  | fix₂ _ IH =>
    apply IH
  | app₁ _ _ IH₀ IH₁
  | app₂ _ _ IH₀ IH₁
  | binary₁ _ _ _ IH₀ IH₁
  | binary₂ _ _ _ IH₀ IH₁
  | lets _ _ IH₀ IH₁
  | let𝕔 _ _ IH₀ IH₁
  | store₁ _ _ IH₀ IH₁
  | store₂ _ _ IH₀ IH₁ =>
    constructor
    . intro Hclose; constructor
      apply (IH₀ _).mp; apply Hclose.left
      apply (IH₁ _).mp; apply Hclose.right
    . intro Hclose; constructor
      apply (IH₀ _).mpr; apply Hclose.left
      apply (IH₁ _).mpr; apply Hclose.right
  | lit| loc| unit => simp
  | ifz₁ _ _ _ IH₀ IH₁ IH₂
  | ifz₂ _ _ _ IH₀ IH₁ IH₂ =>
    constructor
    . intro Hclose
      constructor
      apply (IH₀ _).mp; apply Hclose.left; constructor
      apply (IH₁ _).mp; apply Hclose.right.left
      apply (IH₂ _).mp; apply Hclose.right.right
    . intro Hclose
      constructor
      apply (IH₀ _).mpr; apply Hclose.left; constructor
      apply (IH₁ _).mpr; apply Hclose.right.left
      apply (IH₂ _).mpr; apply Hclose.right.right

lemma open_subst_closed : ∀ x e v i, closed_at e x → closed_at v x → closed_at (opening i v e) x :=
  by
  intros x e v i He Hv
  induction e generalizing i with
  | bvar j =>
    simp; by_cases HEq : j = i
    . rw [if_pos HEq]; apply Hv
    . rw [if_neg HEq]; simp
  | fvar => apply He
  | lit| loc| unit => simp
  | lam _ IH
  | lift _ IH
  | lam𝕔 _ IH
  | code _ IH
  | reflect _ IH
  | run _ IH
  | load₁ _ IH
  | alloc₁ _ IH
  | load₂ _ IH
  | alloc₂ _ IH
  | fix₁ _ IH
  | fix₂ _ IH =>
    apply IH; apply He
  | app₁ _ _ IH₀ IH₁
  | app₂ _ _ IH₀ IH₁
  | binary₁ _ _ _ IH₀ IH₁
  | binary₂ _ _ _ IH₀ IH₁
  | lets _ _ IH₀ IH₁
  | let𝕔 _ _ IH₀ IH₁
  | store₁ _ _ IH₀ IH₁
  | store₂ _ _ IH₀ IH₁ =>
    constructor
    apply IH₀; apply He.left
    apply IH₁; apply He.right
  | ifz₁ _ _ _ IH₀ IH₁ IH₂
  | ifz₂ _ _ _ IH₀ IH₁ IH₂ =>
    simp; constructor
    apply IH₀; apply He.left; constructor
    apply IH₁; apply He.right.left
    apply IH₂; apply He.right.right

lemma open_closed : ∀ e x i, closed_at e x → closed_at (opening i (.fvar x) e) (x + 1) :=
  by
  intros e x i
  induction e generalizing i with
  | fvar y => simp; omega
  | bvar j =>
    by_cases HEq : j = i
    . rw [HEq]; simp
    . simp; rw [if_neg HEq]; simp
  | lam _ IH
  | lift _ IH
  | lam𝕔 _ IH
  | code _ IH
  | reflect _ IH
  | run _ IH
  | load₁ _ IH
  | alloc₁ _ IH
  | load₂ _ IH
  | alloc₂ _ IH
  | fix₁ _ IH
  | fix₂ _ IH =>
    apply IH
  | app₁ _ _ IH₀ IH₁
  | app₂ _ _ IH₀ IH₁
  | binary₁ _ _ _ IH₀ IH₁
  | binary₂ _ _ _ IH₀ IH₁
  | lets _ _ IH₀ IH₁
  | let𝕔 _ _ IH₀ IH₁
  | store₁ _ _ IH₀ IH₁
  | store₂ _ _ IH₀ IH₁ =>
    intro Hclose; constructor
    apply IH₀; apply Hclose.left
    apply IH₁; apply Hclose.right
  | lit| loc| unit => simp
  | ifz₁ _ _ _ IH₀ IH₁ IH₂
  | ifz₂ _ _ _ IH₀ IH₁ IH₂ =>
    intro Hclose; constructor
    apply IH₀; apply Hclose.left; constructor
    apply IH₁; apply Hclose.right.left
    apply IH₂; apply Hclose.right.right

lemma close_lc : ∀ e x i j, j < i → lc_at e i → lc_at (closing j x e) i :=
  by
  intros e x i j Hlt
  induction e generalizing i j with
  | fvar y =>
    by_cases HEq : x = y
    . rw [HEq]; simp; omega
    . simp; rw [if_neg HEq]; simp
  | bvar => simp
  | lam _ IH
  | lift _ IH
  | lam𝕔 _ IH
  | code _ IH
  | reflect _ IH
  | run _ IH
  | load₁ _ IH
  | alloc₁ _ IH
  | load₂ _ IH
  | alloc₂ _ IH
  | fix₁ _ IH
  | fix₂ _ IH =>
    apply IH; omega
  | app₁ _ _ IH₀ IH₁
  | app₂ _ _ IH₀ IH₁
  | binary₁ _ _ _ IH₀ IH₁
  | binary₂ _ _ _ IH₀ IH₁
  | lets _ _ IH₀ IH₁
  | let𝕔 _ _ IH₀ IH₁
  | store₁ _ _ IH₀ IH₁
  | store₂ _ _ IH₀ IH₁ =>
    intro Hclose; constructor
    apply IH₀; omega; apply Hclose.left
    apply IH₁; omega; apply Hclose.right
  | lit| loc| unit => simp
  | ifz₁ _ _ _ IH₀ IH₁ IH₂
  | ifz₂ _ _ _ IH₀ IH₁ IH₂ =>
    intro Hclose; constructor
    apply IH₀; omega; apply Hclose.left; constructor
    apply IH₁; omega; apply Hclose.right.left
    apply IH₂; omega; apply Hclose.right.right

lemma lc_opening_id : ∀ e v i, lc_at e i → opening i v e = e :=
  by
  intros e v i Hlc
  induction e generalizing i with
  | fvar y => simp
  | bvar j => simp at *; omega
  | lift _ IH
  | code _ IH
  | reflect _ IH
  | run _ IH
  | lam _ IH
  | lam𝕔 _ IH
  | load₁ _ IH
  | alloc₁ _ IH
  | load₂ _ IH
  | alloc₂ _ IH
  | fix₁ _ IH
  | fix₂ _ IH =>
    simp; apply IH; apply Hlc
  | app₁ _ _ IH₀ IH₁
  | app₂ _ _ IH₀ IH₁
  | binary₁ _ _ _ IH₀ IH₁
  | binary₂ _ _ _ IH₀ IH₁
  | lets _ _ IH₀ IH₁
  | let𝕔 _ _ IH₀ IH₁
  | store₁ _ _ IH₀ IH₁
  | store₂ _ _ IH₀ IH₁ =>
    simp; constructor
    apply IH₀; apply Hlc.left
    apply IH₁; apply Hlc.right
  | lit| loc| unit => simp
  | ifz₁ _ _ _ IH₀ IH₁ IH₂
  | ifz₂ _ _ _ IH₀ IH₁ IH₂ =>
    simp; constructor
    apply IH₀; apply Hlc.left; constructor
    apply IH₁; apply Hlc.right.left
    apply IH₂; apply Hlc.right.right

lemma open_close_id : ∀ i e x, lc_at e i → opening i (.fvar x) (closing i x e) = e :=
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
  | lam _ IH
  | lift _ IH
  | lam𝕔 _ IH
  | code _ IH
  | reflect _ IH
  | run _ IH
  | load₁ _ IH
  | alloc₁ _ IH
  | load₂ _ IH
  | alloc₂ _ IH
  | fix₁ _ IH
  | fix₂ _ IH =>
    simp; apply IH; apply Hlc
  | app₁ _ _ IH₀ IH₁
  | app₂ _ _ IH₀ IH₁
  | binary₁ _ _ _ IH₀ IH₁
  | binary₂ _ _ _ IH₀ IH₁
  | lets _ _ IH₀ IH₁
  | let𝕔 _ _ IH₀ IH₁
  | store₁ _ _ IH₀ IH₁
  | store₂ _ _ IH₀ IH₁ =>
    simp; constructor
    apply IH₀; apply Hlc.left
    apply IH₁; apply Hlc.right
  | lit| loc| unit => rfl
  | ifz₁ _ _ _ IH₀ IH₁ IH₂
  | ifz₂ _ _ _ IH₀ IH₁ IH₂ =>
    simp; constructor
    apply IH₀; apply Hlc.left; constructor
    apply IH₁; apply Hlc.right.left
    apply IH₂; apply Hlc.right.right

lemma open_close_id₀ : ∀ e x, lc e → open₀ x (close₀ x e) = e := by apply open_close_id

lemma close_open_id : ∀ i e x, closed_at e x → closing i x (opening i (.fvar x) e) = e :=
  by
  intros i e x Hclose
  induction e generalizing i with
  | bvar j =>
    by_cases HEq : j = i
    . simp; rw [if_pos HEq]; simp; omega
    . simp; rw [if_neg HEq]; simp
  | fvar y => simp at *; omega
  | lam _ IH
  | lift _ IH
  | lam𝕔 _ IH
  | code _ IH
  | reflect _ IH
  | run _ IH
  | load₁ _ IH
  | alloc₁ _ IH
  | load₂ _ IH
  | alloc₂ _ IH
  | fix₁ _ IH
  | fix₂ _ IH =>
    simp; apply IH; apply Hclose
  | app₁ _ _ IH₀ IH₁
  | app₂ _ _ IH₀ IH₁
  | binary₁ _ _ _ IH₀ IH₁
  | binary₂ _ _ _ IH₀ IH₁
  | lets _ _ IH₀ IH₁
  | let𝕔 _ _ IH₀ IH₁
  | store₁ _ _ IH₀ IH₁
  | store₂ _ _ IH₀ IH₁ =>
    simp; constructor
    apply IH₀; apply Hclose.left
    apply IH₁; apply Hclose.right
  | lit| loc| unit => rfl
  | ifz₁ _ _ _ IH₀ IH₁ IH₂
  | ifz₂ _ _ _ IH₀ IH₁ IH₂ =>
    simp; constructor
    apply IH₀; apply Hclose.left; constructor
    apply IH₁; apply Hclose.right.left
    apply IH₂; apply Hclose.right.right

lemma close_open_id₀ : ∀ e x, closed_at e x → close₀ x (open₀ x e) = e := by apply close_open_id

lemma subst_opening_comm :
    ∀ x y e v i, x ≠ y → lc_at v i → subst x v (opening i (.fvar y) e) = opening i (.fvar y) (subst x v e) :=
  by
  intro x y e v i HNe Hlc
  induction e generalizing i with
  | bvar j =>
    by_cases HEq : j = i
    . simp; rw [if_pos HEq]; simp; omega
    . simp; rw [if_neg HEq]; simp
  | fvar z =>
    by_cases HEq : x = z
    . simp; rw [if_pos HEq]; rw [lc_opening_id]; apply Hlc
    . simp; rw [if_neg HEq]; simp
  | app₁ _ _ IH₀ IH₁
  | app₂ _ _ IH₀ IH₁
  | binary₁ _ _ _ IH₀ IH₁
  | binary₂ _ _ _ IH₀ IH₁
  | store₁ _ _ IH₀ IH₁
  | store₂ _ _ IH₀ IH₁ =>
    simp; constructor
    apply IH₀; apply Hlc
    apply IH₁; apply Hlc
  | lets _ _ IH₀ IH₁
  | let𝕔 _ _ IH₀ IH₁ =>
    simp; constructor
    apply IH₀; apply Hlc
    apply IH₁; apply lc_inc; apply Hlc; omega
  | code _ IH
  | reflect _ IH
  | run _ IH
  | load₁ _ IH
  | alloc₁ _ IH
  | load₂ _ IH
  | alloc₂ _ IH
  | fix₁ _ IH
  | fix₂ _ IH =>
    simp; apply IH; apply Hlc
  | lit| loc| unit => simp
  | lam _ IH
  | lift _ IH
  | lam𝕔 _ IH =>
    simp; apply IH; apply lc_inc; apply Hlc; omega
  | ifz₁ _ _ _ IH₀ IH₁ IH₂
  | ifz₂ _ _ _ IH₀ IH₁ IH₂ =>
    simp; constructor
    apply IH₀; apply Hlc; constructor
    apply IH₁; apply Hlc
    apply IH₂; apply Hlc

lemma subst_open₀_comm : ∀ x y e v, x ≠ y → lc v → subst x v (open₀ y e) = open₀ y (subst x v e) := by
  intros x y e v; apply subst_opening_comm

example : map𝕔₀ (.app₁ (.bvar 0) (.lam (.bvar 1))) = .app₁ (.code (.bvar 0)) (.lam (.code (.bvar 1))) := by simp

lemma maping𝕔_intro :
    ∀ x e i, closed_at e x → closing i x (subst x (.code (.fvar x)) (opening i (.fvar x) e)) = maping𝕔 e i :=
  by
  intros x e i Hclose
  induction e generalizing i with
  | bvar j => by_cases HEq : j = i; rw [HEq]; simp; simp [if_neg HEq]
  | fvar y => simp at *; by_cases HEq : x = y; omega; rw [if_neg HEq]; simp; apply HEq
  | lam _ IH
  | lift _ IH
  | code _ IH
  | reflect _ IH
  | lam𝕔 _ IH
  | run _ IH
  | load₁ _ IH
  | alloc₁ _ IH
  | load₂ _ IH
  | alloc₂ _ IH
  | fix₁ _ IH
  | fix₂ _ IH =>
    simp at *; apply IH; apply Hclose
  | app₁ _ _ IH₀ IH₁
  | app₂ _ _ IH₀ IH₁
  | binary₁ _ _ _ IH₀ IH₁
  | binary₂ _ _ _ IH₀ IH₁
  | lets _ _ IH₀ IH₁
  | let𝕔 _ _ IH₀ IH₁
  | store₁ _ _ IH₀ IH₁
  | store₂ _ _ IH₀ IH₁ =>
    simp at *; constructor
    apply IH₀; apply Hclose.left
    apply IH₁; apply Hclose.right
  | lit| loc| unit => simp
  | ifz₁ _ _ _ IH₀ IH₁ IH₂
  | ifz₂ _ _ _ IH₀ IH₁ IH₂ =>
    simp; constructor
    apply IH₀; apply Hclose.left; constructor
    apply IH₁; apply Hclose.right.left
    apply IH₂; apply Hclose.right.right

lemma map𝕔₀_intro : ∀ x e, closed_at e x → close₀ x (subst x (.code (.fvar x)) (open₀ x e)) = map𝕔₀ e :=
  by
  intro _ _ Hclose
  apply maping𝕔_intro
  apply Hclose

lemma maping𝕔_closed : ∀ x e i, closed_at e x → closed_at (maping𝕔 e i) x :=
  by
  intros x e i He
  induction e generalizing i with
  | bvar j =>
    simp; by_cases HEq : j = i
    . rw [if_pos HEq]; apply He
    . rw [if_neg HEq]; simp
  | fvar => apply He
  | lit| loc| unit => simp
  | lam _ IH
  | lift _ IH
  | lam𝕔 _ IH
  | code _ IH
  | reflect _ IH
  | run _ IH
  | load₁ _ IH
  | alloc₁ _ IH
  | load₂ _ IH
  | alloc₂ _ IH
  | fix₁ _ IH
  | fix₂ _ IH =>
    apply IH; apply He
  | app₁ _ _ IH₀ IH₁
  | app₂ _ _ IH₀ IH₁
  | binary₁ _ _ _ IH₀ IH₁
  | binary₂ _ _ _ IH₀ IH₁
  | lets _ _ IH₀ IH₁
  | let𝕔 _ _ IH₀ IH₁
  | store₁ _ _ IH₀ IH₁
  | store₂ _ _ IH₀ IH₁ =>
    constructor
    apply IH₀; apply He.left
    apply IH₁; apply He.right
  | ifz₁ _ _ _ IH₀ IH₁ IH₂
  | ifz₂ _ _ _ IH₀ IH₁ IH₂ =>
    simp; constructor
    apply IH₀; apply He.left; constructor
    apply IH₁; apply He.right.left
    apply IH₂; apply He.right.right

lemma fv_if_closed_at :
  ∀ x y e,
    closed_at e x →
    y ≥ x →
    y ∉ fv e :=
  by
  intros x y e Hclose HGe HIn
  induction e with
  | bvar => nomatch HIn
  | fvar z =>
    simp at *
    omega
  | lit| loc| unit => nomatch HIn
  | lam _ IH
  | lift _ IH
  | lam𝕔 _ IH
  | code _ IH
  | reflect _ IH
  | run _ IH
  | load₁ _ IH
  | alloc₁ _ IH
  | load₂ _ IH
  | alloc₂ _ IH
  | fix₁ _ IH
  | fix₂ _ IH =>
    apply IH; apply Hclose; apply HIn
  | app₁ _ _ IH₀ IH₁
  | app₂ _ _ IH₀ IH₁
  | binary₁ _ _ _ IH₀ IH₁
  | binary₂ _ _ _ IH₀ IH₁
  | lets _ _ IH₀ IH₁
  | let𝕔 _ _ IH₀ IH₁
  | store₁ _ _ IH₀ IH₁
  | store₂ _ _ IH₀ IH₁ =>
    cases HIn
    case inl H₀ =>
      apply IH₀; apply Hclose.left; apply H₀
    case inr H₁ =>
      apply IH₁; apply Hclose.right; apply H₁
  | ifz₁ _ _ _ IH₀ IH₁ IH₂
  | ifz₂ _ _ _ IH₀ IH₁ IH₂ =>
    cases HIn
    case inl HIn =>
      cases HIn
      case inl H₀ =>
        apply IH₀; apply Hclose.left; apply H₀
      case inr H₁ =>
        apply IH₁; apply Hclose.right.left; apply H₁
    case inr H₂ =>
      apply IH₂; apply Hclose.right.right; apply H₂

lemma fv_opening : ∀ i v e, fv (opening i v e) ⊆ fv v ∪ fv e :=
  by
  intros i v e
  induction e generalizing i with
  | bvar j =>
    simp; by_cases HEq : j = i
    . rw [if_pos HEq]
    . rw [if_neg HEq]; simp
  | fvar z => simp
  | lit| loc| unit => simp
  | lam _ IH
  | lift _ IH
  | lam𝕔 _ IH
  | code _ IH
  | reflect _ IH
  | run _ IH
  | load₁ _ IH
  | alloc₁ _ IH
  | load₂ _ IH
  | alloc₂ _ IH
  | fix₁ _ IH
  | fix₂ _ IH =>
    apply IH
  | app₁ _ _ IH₀ IH₁
  | app₂ _ _ IH₀ IH₁
  | binary₁ _ _ _ IH₀ IH₁
  | binary₂ _ _ _ IH₀ IH₁
  | lets _ _ IH₀ IH₁
  | let𝕔 _ _ IH₀ IH₁
  | store₁ _ _ IH₀ IH₁
  | store₂ _ _ IH₀ IH₁ =>
    simp; constructor
    apply Set.Subset.trans; apply IH₀
    apply Set.union_subset_union; rfl; simp
    apply Set.Subset.trans; apply IH₁
    apply Set.union_subset_union; rfl; simp
  | ifz₁ _ _ _ IH₀ IH₁ IH₂
  | ifz₂ _ _ _ IH₀ IH₁ IH₂ =>
    simp; constructor; constructor
    apply Set.Subset.trans; apply IH₀
    apply Set.union_subset_union; rfl
    rw [Set.union_assoc]; simp
    apply Set.Subset.trans; apply IH₁
    apply Set.union_subset_union; rfl
    rw [Set.union_assoc, Set.union_comm, Set.union_assoc]; simp
    apply Set.Subset.trans; apply IH₂
    apply Set.union_subset_union; rfl
    simp

lemma fv_open₀ :
  ∀ x y e,
    x ∉ fv e →
    x ≠ y →
    x ∉ fv (open₀ y e) :=
  by
  intros x y e HNotIn HNe HIn
  apply HNotIn
  have H : fv (open₀ y e) ⊆ { y } ∪ fv e := by apply fv_opening
  rw [Set.subset_def] at H
  cases (H x HIn)
  case inl => simp at *; omega
  case inr => assumption

lemma fv_closed_at_dec :
  ∀ e x,
    closed_at e (x + 1) →
    x ∉ fv e →
    closed_at e x :=
  by
  intros e x Hclose HFv
  induction e with
  | bvar j => simp
  | fvar y => simp at *; omega
  | lit| loc| unit => simp
  | lift _ IH
  | code _ IH
  | reflect _ IH
  | run _ IH
  | lam _ IH
  | lam𝕔 _ IH
  | load₁ _ IH
  | alloc₁ _ IH
  | load₂ _ IH
  | alloc₂ _ IH
  | fix₁ _ IH
  | fix₂ _ IH =>
    apply IH; apply Hclose; apply HFv
  | app₁ _ _ IH₀ IH₁
  | app₂ _ _ IH₀ IH₁
  | binary₁ _ _ _ IH₀ IH₁
  | binary₂ _ _ _ IH₀ IH₁
  | lets _ _ IH₀ IH₁
  | let𝕔 _ _ IH₀ IH₁
  | store₁ _ _ IH₀ IH₁
  | store₂ _ _ IH₀ IH₁ =>
    simp at HFv; constructor
    apply IH₀; apply Hclose.left; apply HFv.left
    apply IH₁; apply Hclose.right; apply HFv.right
  | ifz₁ _ _ _ IH₀ IH₁ IH₂
  | ifz₂ _ _ _ IH₀ IH₁ IH₂ =>
    simp at HFv; constructor
    apply IH₀; apply Hclose.left; apply HFv.left.left; constructor
    apply IH₁; apply Hclose.right.left; apply HFv.left.right
    apply IH₂; apply Hclose.right.right; apply HFv.right

lemma fv_maping𝕔 : ∀ e i, fv e = fv (maping𝕔 e i) :=
  by
  intros e i
  induction e generalizing i with
  | bvar j =>
    simp; by_cases HEq : j = i
    . rw [if_pos HEq]; rfl
    . rw [if_neg HEq]; rfl
  | fvar => rfl
  | lit| loc| unit => rfl
  | lam _ IH
  | lift _ IH
  | lam𝕔 _ IH
  | code _ IH
  | reflect _ IH
  | run _ IH
  | load₁ _ IH
  | alloc₁ _ IH
  | load₂ _ IH
  | alloc₂ _ IH
  | fix₁ _ IH
  | fix₂ _ IH => apply IH
  | app₁ _ _ IH₀ IH₁
  | app₂ _ _ IH₀ IH₁
  | binary₁ _ _ _ IH₀ IH₁
  | binary₂ _ _ _ IH₀ IH₁
  | lets _ _ IH₀ IH₁
  | let𝕔 _ _ IH₀ IH₁
  | store₁ _ _ IH₀ IH₁
  | store₂ _ _ IH₀ IH₁ =>
    simp; rw [IH₀, IH₁]
  | ifz₁ _ _ _ IH₀ IH₁ IH₂
  | ifz₂ _ _ _ IH₀ IH₁ IH₂ =>
    simp; rw [IH₀, IH₁, IH₂]

lemma fv_empty_iff_closed : ∀ e, fv e = ∅ ↔ closed e :=
  by
  intro e
  induction e with
  | bvar => simp
  | fvar => simp
  | lit| loc| unit => simp
  | lam _ IH
  | lift _ IH
  | lam𝕔 _ IH
  | code _ IH
  | reflect _ IH
  | run _ IH
  | load₁ _ IH
  | alloc₁ _ IH
  | load₂ _ IH
  | alloc₂ _ IH
  | fix₁ _ IH
  | fix₂ _ IH =>
    apply IH
  | app₁ _ _ IH₀ IH₁
  | app₂ _ _ IH₀ IH₁
  | binary₁ _ _ _ IH₀ IH₁
  | binary₂ _ _ _ IH₀ IH₁
  | lets _ _ IH₀ IH₁
  | let𝕔 _ _ IH₀ IH₁
  | store₁ _ _ IH₀ IH₁
  | store₂ _ _ IH₀ IH₁ =>
    constructor
    . intro HFv; simp at HFv
      constructor
      apply IH₀.mp; apply HFv.left
      apply IH₁.mp; apply HFv.right
    . intro Hclose
      simp; constructor
      apply IH₀.mpr; apply Hclose.left
      apply IH₁.mpr; apply Hclose.right
  | ifz₁ _ _ _ IH₀ IH₁ IH₂
  | ifz₂ _ _ _ IH₀ IH₁ IH₂ =>
    constructor
    . intro HFv; simp at HFv
      constructor
      apply IH₀.mp; apply HFv.left.left; constructor
      apply IH₁.mp; apply HFv.left.right
      apply IH₂.mp; apply HFv.right
    . intro Hclose
      simp; constructor; constructor
      apply IH₀.mpr; apply Hclose.left
      apply IH₁.mpr; apply Hclose.right.left
      apply IH₂.mpr; apply Hclose.right.right

lemma fv_closing : ∀ i x e, fv (closing i x e) = fv e \ { x } :=
  by
  intros i x e
  induction e generalizing i with
  | bvar => simp
  | fvar y =>
    simp; by_cases HEq : x = y
    . rw [if_pos HEq]
      rw [HEq]; simp
    . rw [if_neg HEq]
      rw [Set.diff_singleton_eq_self]
      rfl; apply HEq
  | lit| loc| unit => simp
  | lam _ IH
  | lift _ IH
  | lam𝕔 _ IH
  | code _ IH
  | reflect _ IH
  | run _ IH
  | load₁ _ IH
  | alloc₁ _ IH
  | load₂ _ IH
  | alloc₂ _ IH
  | fix₁ _ IH
  | fix₂ _ IH =>
    apply IH
  | app₁ _ _ IH₀ IH₁
  | app₂ _ _ IH₀ IH₁
  | binary₁ _ _ _ IH₀ IH₁
  | binary₂ _ _ _ IH₀ IH₁
  | lets _ _ IH₀ IH₁
  | let𝕔 _ _ IH₀ IH₁
  | store₁ _ _ IH₀ IH₁
  | store₂ _ _ IH₀ IH₁ =>
    simp; rw [IH₀, IH₁]
    rw [Set.union_diff_distrib]
  | ifz₁ _ _ _ IH₀ IH₁ IH₂
  | ifz₂ _ _ _ IH₀ IH₁ IH₂ =>
    simp; rw [IH₀, IH₁, IH₂]
    rw [Set.union_diff_distrib]
    rw [Set.union_diff_distrib]

lemma fv_subset_closed :
  ∀ e₀ e₁ x,
    fv e₁ ⊆ fv e₀ →
    closed_at e₀ x →
    closed_at e₁ x :=
  by
  intros e₀ e₁ x HFv Hclose
  induction e₁ with
  | bvar| lit| loc| unit => simp
  | fvar y =>
    simp at *
    have _ : ¬y ≥ x := by
      intro HGe
      apply fv_if_closed_at; apply Hclose
      apply HGe; apply HFv
    omega
  | lam _ IH
  | lift _ IH
  | lam𝕔 _ IH
  | code _ IH
  | reflect _ IH
  | run _ IH
  | load₁ _ IH
  | alloc₁ _ IH
  | load₂ _ IH
  | alloc₂ _ IH
  | fix₁ _ IH
  | fix₂ _ IH =>
    apply IH; apply HFv
  | app₁ _ _ IH₀ IH₁
  | app₂ _ _ IH₀ IH₁
  | binary₁ _ _ _ IH₀ IH₁
  | binary₂ _ _ _ IH₀ IH₁
  | lets _ _ IH₀ IH₁
  | let𝕔 _ _ IH₀ IH₁
  | store₁ _ _ IH₀ IH₁
  | store₂ _ _ IH₀ IH₁ =>
    simp at HFv; constructor
    apply IH₀; apply HFv.left
    apply IH₁; apply HFv.right
  | ifz₁ _ _ _ IH₀ IH₁ IH₂
  | ifz₂ _ _ _ IH₀ IH₁ IH₂ =>
    simp at HFv; constructor
    apply IH₀; apply HFv.left.left; constructor
    apply IH₁; apply HFv.left.right
    apply IH₂; apply HFv.right
