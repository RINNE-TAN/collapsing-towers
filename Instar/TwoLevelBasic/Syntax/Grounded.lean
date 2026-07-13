import Instar.TwoLevelBasic.Syntax.Transform

@[simp]
def grounded (e : Expr) : Prop :=
  match e with
  | .bvar _ => true
  | .fvar _ => true
  | .lam e => grounded e
  | .lift _ => false
  | .app₁ f arg => grounded f ∧ grounded arg
  | .app₂ _ _ => false
  | .lit _ => true
  | .run _ => false
  | .code _ => false
  | .reflect _ => false
  | .lam𝕔 _ => false
  | .lets b e => grounded b ∧ grounded e
  | .lets𝕔 _ _ => false

lemma grounded.under_erase : ∀ e, grounded ⎸e⎹ :=
  by
  intros e
  induction e with
  | bvar| fvar| lit => simp
  | lam _ IH
  | lift _ IH
  | lam𝕔 _ IH
  | code _ IH
  | reflect _ IH
  | run _ IH =>
    simp [IH]
  | app₁ _ _ IH₀ IH₁
  | app₂ _ _ IH₀ IH₁
  | lets _ _ IH₀ IH₁
  | lets𝕔 _ _ IH₀ IH₁ =>
    simp [IH₀, IH₁]

lemma erasable.lift : ∀ e₀ e₁, ⎸e₀⎹ ≠ Expr.lift e₁ :=
  by
  intros e₀ e₁
  induction e₀ <;> simp
  all_goals next IH => apply IH

lemma erasable.run : ∀ e₀ e₁, ⎸e₀⎹ ≠ Expr.run e₁ :=
  by
  intros e₀ e₁
  induction e₀ <;> simp
  all_goals next IH => apply IH

lemma erasable.code : ∀ e₀ e₁, ⎸e₀⎹ ≠ Expr.code e₁ :=
  by
  intros e₀ e₁
  induction e₀ <;> simp
  all_goals next IH => apply IH

lemma erasable.reflect : ∀ e₀ e₁, ⎸e₀⎹ ≠ Expr.reflect e₁ :=
  by
  intros e₀ e₁
  induction e₀ <;> simp
  all_goals next IH => apply IH

lemma grounded_iff_erase_identity : ∀ e, grounded e ↔ ⎸e⎹ = e :=
  by
  intros e
  induction e with
  | bvar| fvar| app₂| lit| lam𝕔| lets𝕔 => simp
  | lam _ IH =>
    simp [IH]
  | app₁ _ _ IH₀ IH₁
  | lets _ _ IH₀ IH₁ =>
    simp [IH₀, IH₁]
  | lift => simp; apply erasable.lift
  | run => simp; apply erasable.run
  | code => simp; apply erasable.code
  | reflect => simp; apply erasable.reflect

lemma grounded.under_opening : ∀ e i x, grounded e ↔ grounded ({i ↦ x} e) :=
  by
  intros e i x
  induction e generalizing i with
  | fvar| app₂| lit| lam𝕔| lets𝕔| lift| run| code| reflect => simp
  | bvar j =>
    by_cases HEq : j = i
    . simp [if_pos HEq]
    . simp [if_neg HEq]
  | lam _ IH =>
    simp; rw [IH]
  | app₁ _ _ IH₀ IH₁
  | lets _ _ IH₀ IH₁ =>
    simp; rw [IH₀, IH₁]

lemma grounded.under_subst : ∀ e v x, grounded v → grounded e → grounded (subst x v e) :=
  by
  intros e v x
  induction e with
  | bvar| app₂| lit| lam𝕔| lets𝕔| lift| run| code| reflect => simp
  | fvar y =>
    intros Hv
    by_cases HEq : x = y
    . simp [if_pos HEq, Hv]
    . simp [if_neg HEq]
  | lam _ IH => simp; apply IH
  | app₁ _ _ IH₀ IH₁
  | lets _ _ IH₀ IH₁ =>
    simp; intros Hv H₀ H₁; constructor
    apply IH₀; apply Hv; apply H₀
    apply IH₁; apply Hv; apply H₁

lemma grounded.under_opening_value : ∀ e v i, grounded v → grounded e → grounded (opening i v e) :=
  by
  intros e v i
  induction e generalizing i with
  | fvar| app₂| lit| lam𝕔| lets𝕔| lift| run| code| reflect => simp
  | bvar j =>
    simp; intros Hv
    by_cases HEq : j = i
    . simp [if_pos HEq, Hv]
    . simp [if_neg HEq]
  | lam _ IH => simp; apply IH
  | app₁ _ _ IH₀ IH₁
  | lets _ _ IH₀ IH₁ =>
    simp; intros Hv H₀ H₁; constructor
    apply IH₀; apply Hv; apply H₀
    apply IH₁; apply Hv; apply H₁
