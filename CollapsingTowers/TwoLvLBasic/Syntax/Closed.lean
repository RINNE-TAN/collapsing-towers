import CollapsingTowers.TwoLvLBasic.Syntax.SyntacticTrans
import CollapsingTowers.TwoLvLBasic.Syntax.Fv

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

lemma closed.fv_not_in_dec :
  ∀ e x,
    closed_at e (x + 1) →
    x ∉ fv e →
    closed_at e x :=
  by
  intros e x Hclosedd HFv
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
    apply IH; apply Hclosedd; apply HFv
  | app₁ _ _ IH₀ IH₁
  | app₂ _ _ IH₀ IH₁
  | lets _ _ IH₀ IH₁
  | lets𝕔 _ _ IH₀ IH₁ =>
    simp at HFv; constructor
    apply IH₀; apply Hclosedd.left; apply HFv.left
    apply IH₁; apply Hclosedd.right; apply HFv.right

lemma closed.inc : ∀ x y e, closed_at e x → x ≤ y → closed_at e y :=
  by
  intros x y e Hclosed Hxy
  induction e with
  | bvar j => simp
  | fvar z => simp at *; omega
  | app₁ _ _ IH₀ IH₁
  | app₂ _ _ IH₀ IH₁
  | lets _ _ IH₀ IH₁
  | lets𝕔 _ _ IH₀ IH₁ =>
    simp; constructor
    apply IH₀; apply Hclosed.left
    apply IH₁; apply Hclosed.right
  | lit => simp
  | lam _ IH
  | lift _ IH
  | lam𝕔 _ IH
  | code _ IH
  | reflect _ IH
  | run _ IH =>
    simp; apply IH; apply Hclosed

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
    . intro Hclosed; constructor
      apply (IH₀ _).mp; apply Hclosed.left
      apply (IH₁ _).mp; apply Hclosed.right
    . intro Hclosed; constructor
      apply (IH₀ _).mpr; apply Hclosed.left
      apply (IH₁ _).mpr; apply Hclosed.right
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
    intro Hclosed; constructor
    apply IH₀; apply Hclosed.left
    apply IH₁; apply Hclosed.right
  | lit => simp

lemma closed.under_shiftl :
    ∀ x y e n, closed_at e x → closed_at (shiftl_at y n e) (x + n) :=
  by
  intros x y e n Hclosed
  induction e with
  | bvar j => simp
  | fvar z =>
    by_cases HLe : y ≤ z
    . simp; rw [if_pos HLe]; simp; apply Hclosed
    . simp; rw [if_neg HLe]; simp at *; omega
  | app₁ _ _ IH₀ IH₁
  | app₂ _ _ IH₀ IH₁
  | lets _ _ IH₀ IH₁
  | lets𝕔 _ _ IH₀ IH₁ =>
    simp; constructor
    apply IH₀; apply Hclosed.left
    apply IH₁; apply Hclosed.right
  | lit => simp
  | lam _ IH
  | lift _ IH
  | lam𝕔 _ IH
  | code _ IH
  | reflect _ IH
  | run _ IH =>
    simp; apply IH; apply Hclosed

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

lemma closed.under_shiftr : ∀ x e, closed_at e x → closed_at (shiftr_at x e) x :=
  by
  intros x e Hclosed
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
    apply IH₀; apply Hclosed.left
    apply IH₁; apply Hclosed.right
  | lit => simp
  | lam _ IH
  | lift _ IH
  | lam𝕔 _ IH
  | code _ IH
  | reflect _ IH
  | run _ IH =>
    simp; apply IH; apply Hclosed

lemma closed.under_shiftr_dec :
  ∀ x y e, closed_at e (x + y + 1) → y ∉ fv e → closed_at (shiftr_at y e) (x + y) :=
  by
  intros x y e Hclosed HFv
  cases x
  case zero =>
    simp at *
    apply closed.under_shiftr
    apply closed.fv_not_in_dec
    apply Hclosed; apply HFv
  case succ x =>
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
      simp at HFv
      simp; constructor
      apply IH₀; apply HFv.left; apply Hclosed.left
      apply IH₁; apply HFv.right; apply Hclosed.right
    | lit => simp
    | lam _ IH
    | lift _ IH
    | lam𝕔 _ IH
    | code _ IH
    | reflect _ IH
    | run _ IH =>
      apply IH; apply HFv; apply Hclosed

lemma closed.impl_fv :
  ∀ x y e,
    closed_at e x →
    y ≥ x →
    y ∉ fv e :=
  by
  intros x y e Hclosed HGe HIn
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
    apply IH; apply Hclosed; apply HIn
  | app₁ _ _ IH₀ IH₁
  | app₂ _ _ IH₀ IH₁
  | lets _ _ IH₀ IH₁
  | lets𝕔 _ _ IH₀ IH₁ =>
    cases HIn
    case inl H₀ =>
      apply IH₀; apply Hclosed.left; apply H₀
    case inr H₁ =>
      apply IH₁; apply Hclosed.right; apply H₁
