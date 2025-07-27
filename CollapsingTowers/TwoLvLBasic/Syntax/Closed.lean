import CollapsingTowers.TwoLvLBasic.Syntax.Basic
import CollapsingTowers.TwoLvLBasic.Syntax.Opening
import CollapsingTowers.TwoLvLBasic.Syntax.Closing
import CollapsingTowers.TwoLvLBasic.Syntax.Shift
import CollapsingTowers.TwoLvLBasic.Syntax.Subst

-- closedness condition for free variables
@[simp]
def closed_at (e : Expr) (x : ℕ) : Prop :=
  match e with
  | .bvar _ => true
  | .fvar y => y < x
  | .lam e => closed_at e x
  | .lift e => closed_at e x
  | .app₁ f arg => closed_at f x ∧ closed_at arg x
  | .app₂ f arg => closed_at f x ∧ closed_at arg x
  | .lit _ => true
  | .run e => closed_at e x
  | .code e => closed_at e x
  | .reflect e => closed_at e x
  | .lam𝕔 e => closed_at e x
  | .lets b e => closed_at b x ∧ closed_at e x
  | .lets𝕔 b e => closed_at b x ∧ closed_at e x

@[simp]
def closed e := closed_at e 0

lemma closed.inc : ∀ x y e, closed_at e x → x ≤ y → closed_at e y :=
  by
  intros x y e Hclose Hxy
  induction e with
  | bvar j => simp
  | fvar z => simp at *; omega
  | app₁ _ _ IH₀ IH₁
  | app₂ _ _ IH₀ IH₁
  | lets _ _ IH₀ IH₁
  | lets𝕔 _ _ IH₀ IH₁ =>
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

lemma closed.under_shiftl :
    ∀ x y e n, closed_at e x → closed_at (shiftl_at y n e) (x + n) :=
  by
  intros x y e n Hclose
  induction e with
  | bvar j => simp
  | fvar z =>
    by_cases HLe : y ≤ z
    . simp; rw [if_pos HLe]; simp; apply Hclose
    . simp; rw [if_neg HLe]; simp at *; omega
  | app₁ _ _ IH₀ IH₁
  | app₂ _ _ IH₀ IH₁
  | lets _ _ IH₀ IH₁
  | lets𝕔 _ _ IH₀ IH₁ =>
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

lemma closed.under_shiftr : ∀ x e, closed_at e x → closed_at (shiftr_at x e) x :=
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
  | lets _ _ IH₀ IH₁
  | lets𝕔 _ _ IH₀ IH₁ =>
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

lemma closed.under_shiftr_dec : ∀ x y e, y < x → closed_at e (x + 1) → closed_at (shiftr_at y e) x :=
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
  | lets _ _ IH₀ IH₁
  | lets𝕔 _ _ IH₀ IH₁ =>
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

lemma closed.under_subst : ∀ x e v y, closed_at v y → closed_at e y → closed_at (subst x v e) y :=
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
  | lets𝕔 _ _ IH₀ IH₁ =>
    constructor
    apply IH₀; apply Hv; apply He.left
    apply IH₁; apply Hv; apply He.right
  | code _ IH
  | reflect _ IH
  | run _ IH =>
    simp; apply IH; apply Hv; apply He
  | lit => simp

lemma closed.under_subst_dec : ∀ x e v, closed_at v x → closed_at e (x + 1) → closed_at (subst x v e) x :=
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
  | lets𝕔 _ _ IH₀ IH₁ =>
    constructor
    apply IH₀; apply He.left
    apply IH₁; apply He.right
  | code _ IH
  | reflect _ IH
  | run _ IH =>
    simp; apply IH; apply He
  | lit => simp

lemma closed.under_shiftr_subst :
  ∀ x y e v, closed_at e (x + y + 1) → closed_at v y → closed_at (shiftr_at y (subst y v e)) (x + y) :=
  by
  intros x y e v He Hv
  cases x
  case zero =>
    simp at *
    apply closed.under_shiftr
    apply closed.under_subst_dec
    apply Hv; apply He
  case succ x =>
    apply closed.under_shiftr_dec; omega
    apply closed.under_subst
    apply closed.inc; apply Hv; omega
    apply closed.inc; apply He; omega

lemma closed.under_closing : ∀ e x i, closed_at e (x + 1) ↔ closed_at ({i ↤ x} e) x :=
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
  | lets𝕔 _ _ IH₀ IH₁ =>
    constructor
    . intro Hclose; constructor
      apply (IH₀ _).mp; apply Hclose.left
      apply (IH₁ _).mp; apply Hclose.right
    . intro Hclose; constructor
      apply (IH₀ _).mpr; apply Hclose.left
      apply (IH₁ _).mpr; apply Hclose.right
  | lit => simp

lemma closed.under_opening : ∀ e x i, closed_at e x → closed_at ({i ↦ x} e) (x + 1) :=
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
  | lets𝕔 _ _ IH₀ IH₁ =>
    intro Hclose; constructor
    apply IH₀; apply Hclose.left
    apply IH₁; apply Hclose.right
  | lit => simp
