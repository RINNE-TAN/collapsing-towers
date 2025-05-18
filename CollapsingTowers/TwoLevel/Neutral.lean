
import CollapsingTowers.TwoLevel.Basic
import CollapsingTowers.TwoLevel.OpenClose
import CollapsingTowers.TwoLevel.Shift
@[simp]
def neutral (x : ℕ) : Expr -> Prop
  | .bvar _ => true
  | .fvar _ => false
  | .lam₁ e => neutral x e
  | .lam₂ e => neutral x e
  | .app₁ f arg => neutral x f ∧ neutral x arg
  | .app₂ f arg => neutral x f ∧ neutral x arg
  | .lit₁ _ => true
  | .lit₂ n => neutral x n
  | .plus₁ l r => neutral x l ∧ neutral x r
  | .plus₂ l r => neutral x l ∧ neutral x r
  | .code e => closed_at e x
  | .reflect e => closed_at e x
  | .lam𝕔 e => neutral x e
  | .lets b e => neutral x b ∧ neutral x e
  | .let𝕔 b e => closed_at b x ∧ neutral x e

@[simp]
def neutral_db (i : ℕ) : Expr -> Prop
  | .bvar j => j ≠ i
  | .fvar _ => true
  | .lam₁ e => neutral_db (i + 1) e
  | .lam₂ e => neutral_db i e
  | .app₁ f arg => neutral_db i f ∧ neutral_db i arg
  | .app₂ f arg => neutral_db i f ∧ neutral_db i arg
  | .lit₁ _ => true
  | .lit₂ n => neutral_db i n
  | .plus₁ l r => neutral_db i l ∧ neutral_db i r
  | .plus₂ l r => neutral_db i l ∧ neutral_db i r
  | .code _ => true
  | .reflect _ => true
  | .lam𝕔 e => neutral_db (i + 1) e
  | .lets b e => neutral_db i b ∧ neutral_db (i + 1) e
  | .let𝕔 _ e => neutral_db (i + 1) e

@[simp]
def neutral_lc : Expr -> Prop :=
  neutral_db 0

theorem neutral_closed_at : ∀ x e, neutral x e -> closed_at e x :=
  by
  intros x e HNe
  induction e generalizing x with
  | bvar| lit₁ => simp
  | code| reflect => apply HNe
  | fvar => nomatch HNe
  | lam₁ _ IH
  | lam₂ _ IH
  | lit₂ _ IH
  | lam𝕔 _ IH =>
    apply IH; apply HNe
  | app₁ _ _ IH₀ IH₁
  | app₂ _ _ IH₀ IH₁
  | plus₁ _ _ IH₀ IH₁
  | plus₂ _ _ IH₀ IH₁
  | lets _ _ IH₀ IH₁ =>
    constructor
    apply IH₀; apply HNe.left
    apply IH₁; apply HNe.right
  | let𝕔 _ _ _ IH =>
    constructor
    apply HNe.left
    apply IH; apply HNe.right

theorem closed_at_neutral : ∀ e, closed_at e 0 -> neutral 0 e :=
  by
  intros e Hclose
  induction e with
  | bvar| lit₁ => simp
  | code| reflect => apply Hclose
  | fvar => nomatch Hclose
  | lam₁ _ IH
  | lam₂ _ IH
  | lit₂ _ IH
  | lam𝕔 _ IH =>
    simp at *; apply IH; apply Hclose
  | app₁ _ _ IH₀ IH₁
  | app₂ _ _ IH₀ IH₁
  | plus₁ _ _ IH₀ IH₁
  | plus₂ _ _ IH₀ IH₁
  | lets _ _ IH₀ IH₁ =>
    constructor
    apply IH₀; apply Hclose.left
    apply IH₁; apply Hclose.right
  | let𝕔 _ _ _ IH =>
    constructor
    apply Hclose.left
    apply IH; apply Hclose.right

theorem neutral_inc : ∀ x e i, neutral x e -> neutral_db i e -> neutral (x + 1) (opening i (.fvar x) e) :=
  by
  intros x e i HNeu HNeulc
  induction e generalizing i with
  | bvar => simp at *; rw [if_neg HNeulc]; simp
  | fvar => nomatch HNeu
  | lit₁ => simp
  | code| reflect => apply open_closed; apply HNeu
  | lam₁ _ IH
  | lam₂ _ IH
  | lit₂ _ IH
  | lam𝕔 _ IH =>
    simp at *; apply IH; apply HNeu; apply HNeulc
  | app₁ _ _ IH₀ IH₁
  | app₂ _ _ IH₀ IH₁
  | plus₁ _ _ IH₀ IH₁
  | plus₂ _ _ IH₀ IH₁
  | lets _ _ IH₀ IH₁ =>
    constructor
    apply IH₀; apply HNeu.left; apply HNeulc.left
    apply IH₁; apply HNeu.right; apply HNeulc.right
  | let𝕔 _ _ _ IH =>
    simp; constructor
    apply open_closed; apply HNeu.left
    apply IH; apply HNeu.right; apply HNeulc

theorem shiftl_neutral_db :
    ∀ x y e n, neutral_db y e -> neutral_db y (shiftl_at x n e) :=
  by
  intros x y e n
  induction e generalizing y with
  | bvar j => simp
  | fvar z =>
    simp; by_cases HLe : x <= z
    . rw [if_pos HLe]; simp
    . rw [if_neg HLe]; simp
  | app₁ _ _ IH₀ IH₁
  | app₂ _ _ IH₀ IH₁
  | plus₁ _ _ IH₀ IH₁
  | plus₂ _ _ IH₀ IH₁
  | lets _ _ IH₀ IH₁ =>
    intro HNeu; simp; constructor
    apply IH₀; apply HNeu.left
    apply IH₁; apply HNeu.right
  | let𝕔 _ _ _ IHe =>
    intro HNeu; simp
    apply IHe; apply HNeu
  | lit₁ => simp
  | lam₁ _ IH
  | lam₂ _ IH
  | lam𝕔 _ IH
  | lit₂ _ IH =>
    simp; apply IH
  | code _ IH
  | reflect _ IH => simp

theorem shiftr_neutral_db :
    ∀ x y e, neutral_db y e -> neutral_db y (shiftr_at x e) :=
  by
  intros x y e
  induction e generalizing y with
  | bvar j => simp
  | fvar z =>
    simp; by_cases HLe : x < z
    . rw [if_pos HLe]; simp
    . rw [if_neg HLe]; simp
  | app₁ _ _ IH₀ IH₁
  | app₂ _ _ IH₀ IH₁
  | plus₁ _ _ IH₀ IH₁
  | plus₂ _ _ IH₀ IH₁
  | lets _ _ IH₀ IH₁ =>
    intro HNeu; simp; constructor
    apply IH₀; apply HNeu.left
    apply IH₁; apply HNeu.right
  | let𝕔 _ _ _ IHe =>
    intro HNeu; simp
    apply IHe; apply HNeu
  | lit₁ => simp
  | lam₁ _ IH
  | lam₂ _ IH
  | lam𝕔 _ IH
  | lit₂ _ IH =>
    simp; apply IH
  | code _ IH
  | reflect _ IH => simp

theorem closedb_at_of_neutral_db : ∀ x e, closedb_at e x -> neutral_db x e :=
  by
  intros x e Hclose
  induction e generalizing x with
  | fvar => simp
  | bvar => simp at *; omega
  | app₁ _ _ IH₀ IH₁
  | app₂ _ _ IH₀ IH₁
  | plus₁ _ _ IH₀ IH₁
  | plus₂ _ _ IH₀ IH₁
  | lets _ _ IH₀ IH₁ =>
    constructor
    apply IH₀; apply Hclose.left
    apply IH₁; apply Hclose.right
  | lit₁| code| reflect => simp
  | lam₁ _ IH
  | lam₂ _ IH
  | lam𝕔 _ IH
  | lit₂ _ IH =>
    apply IH; apply Hclose
  | let𝕔 _ _ _ IH =>
    apply IH; apply Hclose.right

theorem subst_neutral_db :
  ∀ x y v e, neutral_db y e -> closedb_at v y -> neutral_db y (subst x v e) :=
  by
  intros x y v e HNeuE HNeuV
  induction e generalizing y with
  | bvar => apply HNeuE
  | fvar z =>
    simp; by_cases HEq : x = z
    . rw [if_pos HEq]; apply closedb_at_of_neutral_db; apply HNeuV
    . rw [if_neg HEq]; simp
  | app₁ _ _ IH₀ IH₁
  | app₂ _ _ IH₀ IH₁
  | plus₁ _ _ IH₀ IH₁
  | plus₂ _ _ IH₀ IH₁ =>
    constructor
    apply IH₀; apply HNeuE.left; apply HNeuV
    apply IH₁; apply HNeuE.right; apply HNeuV
  | lets _ _ IH₀ IH₁ =>
    constructor
    apply IH₀; apply HNeuE.left; apply HNeuV
    apply IH₁; apply HNeuE.right
    apply closedb_inc; apply HNeuV; omega
  | lit₁| code| reflect => simp
  | lam₂ _ IH
  | lit₂ _ IH =>
    apply IH; apply HNeuE; apply HNeuV
  | lam₁ _ IH
  | lam𝕔 _ IH
  | let𝕔 _ _ _ IH =>
    apply IH; apply HNeuE
    apply closedb_inc; apply HNeuV; omega

theorem maping𝕔_neutral_db : ∀ e i, neutral_db i (maping𝕔 e i) :=
  by
  intros e i
  induction e generalizing i with
  | bvar j =>
    simp; by_cases HEq : j = i
    . rw [if_pos HEq]; simp
    . rw [if_neg HEq]; apply HEq
  | fvar| lit₁| code| reflect => simp
  | app₁ _ _ IH₀ IH₁
  | app₂ _ _ IH₀ IH₁
  | plus₁ _ _ IH₀ IH₁
  | plus₂ _ _ IH₀ IH₁
  | lets _ _ IH₀ IH₁ =>
    constructor; apply IH₀; apply IH₁
  | lam₂ _ IH
  | lit₂ _ IH
  | lam₁ _ IH
  | lam𝕔 _ IH
  | let𝕔 _ _ _ IH =>
    apply IH

theorem opening_neutral_db : ∀ e x i j, neutral_db i e -> neutral_db i (opening j (.fvar x) e) :=
  by
  intros e x i j He
  induction e generalizing i j with
  | bvar k =>
    simp; by_cases HEq : k = j
    . rw [if_pos HEq]; simp
    . rw [if_neg HEq]; apply He
  | fvar| lit₁| code| reflect => simp
  | lam₂ _ IH
  | lit₂ _ IH
  | lam₁ _ IH
  | lam𝕔 _ IH
  | let𝕔 _ _ _ IH =>
    apply IH; apply He
  | app₁ _ _ IH₀ IH₁
  | app₂ _ _ IH₀ IH₁
  | plus₁ _ _ IH₀ IH₁
  | plus₂ _ _ IH₀ IH₁
  | lets _ _ IH₀ IH₁ =>
    constructor
    apply IH₀; apply He.left
    apply IH₁; apply He.right

theorem swapdb_neutral_db :
  ∀ e i j,
  neutral_db j e ->
  neutral_db i (swapdb i j e) :=
  by
  intros e i j HNeu
  induction e generalizing i j with
  | bvar k =>
    simp at *; rw [if_neg HNeu]
    by_cases HEq : k = i
    . rw [if_pos HEq]; simp; omega
    . rw [if_neg HEq]; simp; omega
  | fvar| lit₁| code| reflect => simp
  | lam₂ _ IH
  | lit₂ _ IH
  | lam₁ _ IH
  | lam𝕔 _ IH
  | let𝕔 _ _ _ IH =>
    apply IH; apply HNeu
  | app₁ _ _ IH₀ IH₁
  | app₂ _ _ IH₀ IH₁
  | plus₁ _ _ IH₀ IH₁
  | plus₂ _ _ IH₀ IH₁
  | lets _ _ IH₀ IH₁ =>
    constructor
    apply IH₀; apply HNeu.left
    apply IH₁; apply HNeu.right

theorem maping𝕔_neutral : ∀ e x i, neutral x e -> neutral x (maping𝕔 e i) :=
  by
  intros e x i HNeu
  induction e generalizing i with
  | bvar j =>
    simp; by_cases HEq : j = i
    . rw [if_pos HEq]; simp
    . rw [if_neg HEq]; simp
  | fvar => nomatch HNeu
  | lit₁ => simp
  | code _ IH| reflect _ IH => apply maping𝕔_closed; apply HNeu
  | app₁ _ _ IH₀ IH₁
  | app₂ _ _ IH₀ IH₁
  | plus₁ _ _ IH₀ IH₁
  | plus₂ _ _ IH₀ IH₁
  | lets _ _ IH₀ IH₁ =>
    constructor
    apply IH₀; apply HNeu.left
    apply IH₁; apply HNeu.right
  | lam₂ _ IH
  | lit₂ _ IH
  | lam₁ _ IH
  | lam𝕔 _ IH =>
    simp at *
    apply IH; apply HNeu
  | let𝕔 _ _ _ IHe =>
    constructor
    apply maping𝕔_closed; apply HNeu.left
    apply IHe; apply HNeu.right

theorem neutral_closing : ∀ x e i, neutral (x + 1) e -> neutral x (closing i x e) :=
  by
  intros x e i HNeu
  induction e generalizing i with
  | bvar => simp
  | fvar => nomatch HNeu
  | lit₁ => simp
  | code| reflect => apply close_closed; apply HNeu
  | lam₁ _ IH
  | lam₂ _ IH
  | lit₂ _ IH
  | lam𝕔 _ IH =>
    simp at *; apply IH; apply HNeu
  | app₁ _ _ IH₀ IH₁
  | app₂ _ _ IH₀ IH₁
  | plus₁ _ _ IH₀ IH₁
  | plus₂ _ _ IH₀ IH₁
  | lets _ _ IH₀ IH₁ =>
    constructor
    apply IH₀; apply HNeu.left
    apply IH₁; apply HNeu.right
  | let𝕔 _ _ _ IH =>
    constructor
    apply close_closed; apply HNeu.left
    apply IH; apply HNeu.right

theorem neutral_db_closing : ∀ x e i, closedb_at e i -> neutral (x + 1) e -> neutral_db i (closing i x e) :=
  by
  intros x e i Hlc HNeu
  induction e generalizing i with
  | bvar => simp at *; omega
  | fvar => nomatch HNeu
  | lit₁ => simp
  | code| reflect => simp
  | lam₂ _ IH
  | lit₂ _ IH
  | lam₁ _ IH
  | lam𝕔 _ IH =>
    simp at *; apply IH; apply Hlc; apply HNeu
  | app₁ _ _ IH₀ IH₁
  | app₂ _ _ IH₀ IH₁
  | plus₁ _ _ IH₀ IH₁
  | plus₂ _ _ IH₀ IH₁
  | lets _ _ IH₀ IH₁ =>
    constructor
    apply IH₀; apply Hlc.left; apply HNeu.left
    apply IH₁; apply Hlc.right; apply HNeu.right
  | let𝕔 _ _ _ IH => apply IH; apply Hlc.right; apply HNeu.right

theorem neutral_opening : ∀ x e v i, neutral x e -> neutral x v -> neutral x (opening i v e) :=
  by
  intros x e v i He Hv
  induction e generalizing i with
  | bvar j =>
    simp; by_cases HEq : j = i
    . rw [if_pos HEq]; apply Hv
    . rw [if_neg HEq]; simp
  | fvar => nomatch He
  | lit₁ => simp
  | code| reflect =>
    apply open_subst_closed; apply He
    apply neutral_closed_at; apply Hv
  | lam₁ _ IH
  | lam₂ _ IH
  | lit₂ _ IH
  | lam𝕔 _ IH => apply IH; apply He
  | app₁ _ _ IH₀ IH₁
  | app₂ _ _ IH₀ IH₁
  | plus₁ _ _ IH₀ IH₁
  | plus₂ _ _ IH₀ IH₁
  | lets _ _ IH₀ IH₁ =>
    constructor
    apply IH₀; apply He.left
    apply IH₁; apply He.right
  | let𝕔 _ _ _ IH =>
    constructor
    apply open_subst_closed; apply He.left
    apply neutral_closed_at; apply Hv
    apply IH; apply He.right

theorem swapdb_neutral : ∀ e x i j, neutral x e -> neutral x (swapdb i j e) :=
  by
  intros e x i j HNeu
  induction e generalizing i j with
  | bvar k =>
    simp; by_cases HEq : k = i
    . rw [if_pos HEq]; simp
    . rw [if_neg HEq]
      by_cases HEq : k = j
      . rw [if_pos HEq]; simp
      . rw [if_neg HEq]; simp
  | fvar => nomatch HNeu
  | lit₁ => simp
  | code _ IH| reflect _ IH =>
    apply swapdb_closed; apply HNeu
  | app₁ _ _ IH₀ IH₁
  | app₂ _ _ IH₀ IH₁
  | plus₁ _ _ IH₀ IH₁
  | plus₂ _ _ IH₀ IH₁
  | lets _ _ IH₀ IH₁ =>
    constructor
    apply IH₀; apply HNeu.left
    apply IH₁; apply HNeu.right
  | lam₂ _ IH
  | lit₂ _ IH
  | lam₁ _ IH
  | lam𝕔 _ IH =>
    simp at *
    apply IH; apply HNeu
  | let𝕔 _ _ _ IHe =>
    constructor
    apply swapdb_closed; apply HNeu.left
    apply IHe; apply HNeu.right
