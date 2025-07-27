import CollapsingTowers.TwoLvLBasic.Syntax.Basic
import CollapsingTowers.TwoLvLBasic.Syntax.Opening
import CollapsingTowers.TwoLvLBasic.Syntax.Closing
import CollapsingTowers.TwoLvLBasic.Syntax.Subst

-- closedness condition for bound variables
@[simp]
def lc_at (e : Expr) (i : ℕ) : Prop :=
  match e with
  | .bvar j => j < i
  | .fvar _ => true
  | .lam e => lc_at e (i + 1)
  | .lift e => lc_at e i
  | .app₁ f arg => lc_at f i ∧ lc_at arg i
  | .app₂ f arg => lc_at f i ∧ lc_at arg i
  | .lit _ => true
  | .run e => lc_at e i
  | .code e => lc_at e i
  | .reflect e => lc_at e i
  | .lam𝕔 e => lc_at e (i + 1)
  | .lets b e => lc_at b i ∧ lc_at e (i + 1)
  | .lets𝕔 b e => lc_at b i ∧ lc_at e (i + 1)

@[simp]
def lc e := lc_at e 0

lemma lc.inc:
  ∀ e i j,
    lc_at e i → i ≤ j →
    lc_at e j :=
  by
  intros e i j Hclosed HLe
  induction e generalizing i j with
  | bvar => simp at *; omega
  | fvar => simp
  | lam _ IH
  | lift _ IH
  | lam𝕔 _ IH
  | code _ IH
  | reflect _ IH
  | run _ IH =>
    apply IH; apply Hclosed; omega
  | app₁ _ _ IH₀ IH₁
  | app₂ _ _ IH₀ IH₁
  | lets _ _ IH₀ IH₁
  | lets𝕔 _ _ IH₀ IH₁ =>
    apply And.intro
    . apply IH₀; apply Hclosed.left; omega
    . apply IH₁; apply Hclosed.right; omega
  | lit => simp

lemma lc.under_opening : ∀ i x e, lc_at ({i ↦ x} e) i ↔ lc_at e (i + 1) :=
  by
  intros i x e
  induction e generalizing i with
  | bvar j =>
    by_cases HEq : j = i
    . simp [if_pos HEq]; omega
    . simp [if_neg HEq]; omega
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
  | lets𝕔 _ _ IH₀ IH₁ =>
    constructor
    . intro Hlc
      constructor
      apply (IH₀ _).mp; apply Hlc.left
      apply (IH₁ _).mp; apply Hlc.right
    . intro Hlc
      constructor
      apply (IH₀ _).mpr; apply Hlc.left
      apply (IH₁ _).mpr; apply Hlc.right

lemma lc.under_closing : ∀ e x i j, j < i → lc_at e i → lc_at ({j ↤ x} e) i :=
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
  | lets𝕔 _ _ IH₀ IH₁ =>
    intro Hlc; constructor
    apply IH₀; omega; apply Hlc.left
    apply IH₁; omega; apply Hlc.right
  | lit => simp

lemma lc.under_subst : ∀ x e v i, lc_at v i → lc_at e i → lc_at (subst x v e) i :=
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
    apply IH; apply lc.inc
    apply Hv; omega; apply He
  | app₁ _ _ IH₀ IH₁
  | app₂ _ _ IH₀ IH₁ =>
    constructor
    apply IH₀; apply Hv; apply He.left
    apply IH₁; apply Hv; apply He.right
  | lets _ _ IHb IH
  | lets𝕔 _ _ IHb IH =>
    constructor
    apply IHb; apply Hv; apply He.left
    apply IH; apply lc.inc
    apply Hv; omega; apply He.right
  | code _ IH
  | reflect _ IH
  | run _ IH =>
    simp; apply IH; apply Hv; apply He
  | lit => simp
