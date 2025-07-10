
import Mathlib.Data.Set.Insert
import CollapsingTowers.TwoLevelBasic.Syntax
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
  | .run e => .run (subst x v e)
  | .code e => .code (subst x v e)
  | .reflect e => .reflect (subst x v e)
  | .lam𝕔 e => .lam𝕔 (subst x v e)
  | .lets b e => .lets (subst x v b) (subst x v e)
  | .let𝕔 b e => .let𝕔 (subst x v b) (subst x v e)

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
  | .run e => .run (opening i x e)
  | .code e => .code (opening i x e)
  | .reflect e => .reflect (opening i x e)
  | .lam𝕔 e => .lam𝕔 (opening (i + 1) x e)
  | .lets b e => .lets (opening i x b) (opening (i + 1) x e)
  | .let𝕔 b e => .let𝕔 (opening i x b) (opening (i + 1) x e)

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
  | .run e => .run (closing i x e)
  | .code e => .code (closing i x e)
  | .reflect e => .reflect (closing i x e)
  | .lam𝕔 e => .lam𝕔 (closing (i + 1) x e)
  | .lets b e => .lets (closing i x b) (closing (i + 1) x e)
  | .let𝕔 b e => .let𝕔 (closing i x b) (closing (i + 1) x e)

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
  | .run e => closed_at e f
  | .code e => closed_at e f
  | .reflect e => closed_at e f
  | .lam𝕔 e => closed_at e f
  | .lets b e => closed_at b f ∧ closed_at e f
  | .let𝕔 b e => closed_at b f ∧ closed_at e f

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
  | .run e => lc_at e b
  | .code e => lc_at e b
  | .reflect e => lc_at e b
  | .lam𝕔 e => lc_at e (b + 1)
  | .lets e1 e2 => lc_at e1 b ∧ lc_at e2 (b + 1)
  | .let𝕔 e1 e2 => lc_at e1 b ∧ lc_at e2 (b + 1)

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
  | .run e => .run (maping𝕔 e i)
  | .code e => .code (maping𝕔 e i)
  | .reflect e => .reflect (maping𝕔 e i)
  | .lam𝕔 e => .lam𝕔 (maping𝕔 e (i + 1))
  | .lets b e => .lets (maping𝕔 b i) (maping𝕔 e (i + 1))
  | .let𝕔 b e => .let𝕔 (maping𝕔 b i) (maping𝕔 e (i + 1))

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
  | .run e => fv e
  | .code e => fv e
  | .reflect e => fv e
  | .lam𝕔 e => fv e
  | .lets b e => fv b ∪ fv e
  | .let𝕔 b e => fv b ∪ fv e

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
  | run _ IH =>
    simp; apply IH; apply Hclosed
  | app₁ _ _ IH₀ IH₁
  | app₂ _ _ IH₀ IH₁
  | lets _ _ IH₀ IH₁
  | let𝕔 _ _ IH₀ IH₁ =>
    simp; constructor
    apply IH₀; apply Hclosed.left
    apply IH₁; apply Hclosed.right
  | lit => simp

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
  | run _ IH =>
    simp; apply IH; apply He
  | app₁ _ _ IH₀ IH₁
  | app₂ _ _ IH₀ IH₁ =>
    simp; constructor
    apply IH₀; apply He.left
    apply IH₁; apply He.right
  | lets _ _ IHb IH
  | let𝕔 _ _ IHb IH =>
    simp; constructor
    apply IHb; apply He.left
    apply IH; apply He.right
  | lit => simp

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
  | run _ IH =>
    apply IH; apply Hclose; omega
  | app₁ _ _ IH₀ IH₁
  | app₂ _ _ IH₀ IH₁
  | lets _ _ IH₀ IH₁
  | let𝕔 _ _ IH₀ IH₁ =>
    apply And.intro
    . apply IH₀; apply Hclose.left; omega
    . apply IH₁; apply Hclose.right; omega
  | lit => simp

lemma closed_inc : ∀ x y e, closed_at e x → x ≤ y → closed_at e y :=
  by
  intros x y e Hclose Hxy
  induction e with
  | bvar j => simp
  | fvar z => simp at *; omega
  | app₁ _ _ IH₀ IH₁
  | app₂ _ _ IH₀ IH₁
  | lets _ _ IH₀ IH₁
  | let𝕔 _ _ IH₀ IH₁ =>
    simp; constructor
    apply IH₀; apply Hclose.left
    apply IH₁; apply Hclose.right
  | lit => simp
  | lam _ IH
  | lift _ IH
  | lam𝕔 _ IH
  | code _ IH
  | reflect _ IH
  | run _ IH =>
    simp; apply IH; apply Hclose

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
  | app₂ _ _ IH₀ IH₁ =>
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
  | run _ IH =>
    simp; apply IH; apply Hv; apply He
  | lit => simp

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
  | lets _ _ IH₀ IH₁
  | let𝕔 _ _ IH₀ IH₁ =>
    constructor
    apply IH₀; apply Hv; apply He.left
    apply IH₁; apply Hv; apply He.right
  | code _ IH
  | reflect _ IH
  | run _ IH =>
    simp; apply IH; apply Hv; apply He
  | lit => simp

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
  | lets _ _ IH₀ IH₁
  | let𝕔 _ _ IH₀ IH₁ =>
    constructor
    apply IH₀; apply He.left
    apply IH₁; apply He.right
  | code _ IH
  | reflect _ IH
  | run _ IH =>
    simp; apply IH; apply He
  | lit => simp

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
  | lit => simp
  | lam _ IH
  | lift _ IH
  | lam𝕔 _ IH
  | code _ IH
  | reflect _ IH
  | run _ IH =>
    apply IH
  | app₁ _ _ IH₀ IH₁
  | app₂ _ _ IH₀ IH₁
  | lets _ _ IH₀ IH₁
  | let𝕔 _ _ IH₀ IH₁ =>
    constructor
    . intro Hlc
      constructor
      apply (IH₀ _).mp; apply Hlc.left
      apply (IH₁ _).mp; apply Hlc.right
    . intro Hlc
      constructor
      apply (IH₀ _).mpr; apply Hlc.left
      apply (IH₁ _).mpr; apply Hlc.right

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
  | run _ IH =>
    apply IH
  | app₁ _ _ IH₀ IH₁
  | app₂ _ _ IH₀ IH₁
  | lets _ _ IH₀ IH₁
  | let𝕔 _ _ IH₀ IH₁ =>
    constructor
    . intro Hclose; constructor
      apply (IH₀ _).mp; apply Hclose.left
      apply (IH₁ _).mp; apply Hclose.right
    . intro Hclose; constructor
      apply (IH₀ _).mpr; apply Hclose.left
      apply (IH₁ _).mpr; apply Hclose.right
  | lit => simp

lemma open_subst_closed : ∀ x e v i, closed_at e x → closed_at v x → closed_at (opening i v e) x :=
  by
  intros x e v i He Hv
  induction e generalizing i with
  | bvar j =>
    simp; by_cases HEq : j = i
    . rw [if_pos HEq]; apply Hv
    . rw [if_neg HEq]; simp
  | fvar => apply He
  | lit => simp
  | lam _ IH
  | lift _ IH
  | lam𝕔 _ IH
  | code _ IH
  | reflect _ IH
  | run _ IH =>
    apply IH; apply He
  | app₁ _ _ IH₀ IH₁
  | app₂ _ _ IH₀ IH₁
  | lets _ _ IH₀ IH₁
  | let𝕔 _ _ IH₀ IH₁ =>
    constructor
    apply IH₀; apply He.left
    apply IH₁; apply He.right

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
  | run _ IH =>
    apply IH
  | app₁ _ _ IH₀ IH₁
  | app₂ _ _ IH₀ IH₁
  | lets _ _ IH₀ IH₁
  | let𝕔 _ _ IH₀ IH₁ =>
    intro Hclose; constructor
    apply IH₀; apply Hclose.left
    apply IH₁; apply Hclose.right
  | lit => simp

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
  | run _ IH =>
    apply IH; omega
  | app₁ _ _ IH₀ IH₁
  | app₂ _ _ IH₀ IH₁
  | lets _ _ IH₀ IH₁
  | let𝕔 _ _ IH₀ IH₁ =>
    intro Hclose; constructor
    apply IH₀; omega; apply Hclose.left
    apply IH₁; omega; apply Hclose.right
  | lit => simp

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
  | lam𝕔 _ IH =>
    simp; apply IH; apply Hlc
  | app₁ _ _ IH₀ IH₁
  | app₂ _ _ IH₀ IH₁
  | lets _ _ IH₀ IH₁
  | let𝕔 _ _ IH₀ IH₁ =>
    simp; constructor
    apply IH₀; apply Hlc.left
    apply IH₁; apply Hlc.right
  | lit => simp

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
  | run _ IH =>
    simp; apply IH; apply Hlc
  | app₁ _ _ IH₀ IH₁
  | app₂ _ _ IH₀ IH₁
  | lets _ _ IH₀ IH₁
  | let𝕔 _ _ IH₀ IH₁ =>
    simp; constructor
    apply IH₀; apply Hlc.left
    apply IH₁; apply Hlc.right
  | lit => rfl

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
  | run _ IH =>
    simp; apply IH; apply Hclose
  | app₁ _ _ IH₀ IH₁
  | app₂ _ _ IH₀ IH₁
  | lets _ _ IH₀ IH₁
  | let𝕔 _ _ IH₀ IH₁ =>
    simp; constructor
    apply IH₀; apply Hclose.left
    apply IH₁; apply Hclose.right
  | lit => rfl

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
  | app₂ _ _ IH₀ IH₁ =>
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
  | run _ IH =>
    simp; apply IH; apply Hlc
  | lit => simp
  | lam _ IH
  | lift _ IH
  | lam𝕔 _ IH =>
    simp; apply IH; apply lc_inc; apply Hlc; omega

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
  | run _ IH =>
    simp at *; apply IH; apply Hclose
  | app₁ _ _ IH₀ IH₁
  | app₂ _ _ IH₀ IH₁
  | lets _ _ IH₀ IH₁
  | let𝕔 _ _ IH₀ IH₁ =>
    simp at *; constructor
    apply IH₀; apply Hclose.left
    apply IH₁; apply Hclose.right
  | lit => simp

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
  | lit => simp
  | lam _ IH
  | lift _ IH
  | lam𝕔 _ IH
  | code _ IH
  | reflect _ IH
  | run _ IH =>
    apply IH; apply He
  | app₁ _ _ IH₀ IH₁
  | app₂ _ _ IH₀ IH₁
  | lets _ _ IH₀ IH₁
  | let𝕔 _ _ IH₀ IH₁ =>
    constructor
    apply IH₀; apply He.left
    apply IH₁; apply He.right

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
  | lit => nomatch HIn
  | lam _ IH
  | lift _ IH
  | lam𝕔 _ IH
  | code _ IH
  | reflect _ IH
  | run _ IH =>
    apply IH; apply Hclose; apply HIn
  | app₁ _ _ IH₀ IH₁
  | app₂ _ _ IH₀ IH₁
  | lets _ _ IH₀ IH₁
  | let𝕔 _ _ IH₀ IH₁ =>
    cases HIn
    case inl H₀ =>
      apply IH₀; apply Hclose.left; apply H₀
    case inr H₁ =>
      apply IH₁; apply Hclose.right; apply H₁

lemma fv_opening : ∀ i v e, fv (opening i v e) ⊆ fv v ∪ fv e :=
  by
  intros i v e
  induction e generalizing i with
  | bvar j =>
    simp; by_cases HEq : j = i
    . rw [if_pos HEq]
    . rw [if_neg HEq]; simp
  | fvar z => simp
  | lit => simp
  | lam _ IH
  | lift _ IH
  | lam𝕔 _ IH
  | code _ IH
  | reflect _ IH
  | run _ IH =>
    apply IH
  | app₁ _ _ IH₀ IH₁
  | app₂ _ _ IH₀ IH₁
  | lets _ _ IH₀ IH₁
  | let𝕔 _ _ IH₀ IH₁ =>
    simp; constructor
    apply Set.Subset.trans; apply IH₀
    apply Set.union_subset_union; rfl; simp
    apply Set.Subset.trans; apply IH₁
    apply Set.union_subset_union; rfl; simp

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
  | lit => simp
  | lift _ IH
  | code _ IH
  | reflect _ IH
  | run _ IH
  | lam _ IH
  | lam𝕔 _ IH =>
    apply IH; apply Hclose; apply HFv
  | app₁ _ _ IH₀ IH₁
  | app₂ _ _ IH₀ IH₁
  | lets _ _ IH₀ IH₁
  | let𝕔 _ _ IH₀ IH₁ =>
    simp at HFv; constructor
    apply IH₀; apply Hclose.left; apply HFv.left
    apply IH₁; apply Hclose.right; apply HFv.right

lemma fv_maping𝕔 : ∀ e i, fv e = fv (maping𝕔 e i) :=
  by
  intros e i
  induction e generalizing i with
  | bvar j =>
    simp; by_cases HEq : j = i
    . rw [if_pos HEq]; rfl
    . rw [if_neg HEq]; rfl
  | fvar => rfl
  | lit => rfl
  | lam _ IH
  | lift _ IH
  | lam𝕔 _ IH
  | code _ IH
  | reflect _ IH
  | run _ IH => apply IH
  | app₁ _ _ IH₀ IH₁
  | app₂ _ _ IH₀ IH₁
  | lets _ _ IH₀ IH₁
  | let𝕔 _ _ IH₀ IH₁ =>
    simp; rw [IH₀, IH₁]

lemma fv_empty_iff_closed : ∀ e, fv e = ∅ ↔ closed e :=
  by
  intro e
  induction e with
  | bvar => simp
  | fvar => simp
  | lit => simp
  | lam _ IH
  | lift _ IH
  | lam𝕔 _ IH
  | code _ IH
  | reflect _ IH
  | run _ IH =>
    apply IH
  | app₁ _ _ IH₀ IH₁
  | app₂ _ _ IH₀ IH₁
  | lets _ _ IH₀ IH₁
  | let𝕔 _ _ IH₀ IH₁ =>
    constructor
    . intro HFv; simp at HFv
      constructor
      apply IH₀.mp; apply HFv.left
      apply IH₁.mp; apply HFv.right
    . intro Hclose
      simp; constructor
      apply IH₀.mpr; apply Hclose.left
      apply IH₁.mpr; apply Hclose.right

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
  | lit => simp
  | lam _ IH
  | lift _ IH
  | lam𝕔 _ IH
  | code _ IH
  | reflect _ IH
  | run _ IH =>
    apply IH
  | app₁ _ _ IH₀ IH₁
  | app₂ _ _ IH₀ IH₁
  | lets _ _ IH₀ IH₁
  | let𝕔 _ _ IH₀ IH₁ =>
    simp; rw [IH₀, IH₁]
    rw [Set.union_diff_distrib]

lemma fv_subset_closed :
  ∀ e₀ e₁ x,
    fv e₁ ⊆ fv e₀ →
    closed_at e₀ x →
    closed_at e₁ x :=
  by
  intros e₀ e₁ x HFv Hclose
  induction e₁ with
  | bvar| lit => simp
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
  | run _ IH =>
    apply IH; apply HFv
  | app₁ _ _ IH₀ IH₁
  | app₂ _ _ IH₀ IH₁
  | lets _ _ IH₀ IH₁
  | let𝕔 _ _ IH₀ IH₁ =>
    simp at HFv; constructor
    apply IH₀; apply HFv.left
    apply IH₁; apply HFv.right
