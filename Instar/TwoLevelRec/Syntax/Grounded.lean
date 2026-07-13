import Instar.TwoLevelRec.Syntax.Transform

@[simp]
def grounded (e : Expr) : Prop :=
  match e with
  | .bvar _ => true
  | .fvar _ => true
  | .lam e => grounded e
  | .lift _ => false
  | .app₁ f arg => grounded f ∧ grounded arg
  | .app₂ _ _ => false
  | .binary₁ _ l r => grounded l ∧ grounded r
  | .binary₂ _ _ _ => false
  | .lit _ => true
  | .run _ => false
  | .code _ => false
  | .reflect _ => false
  | .lam𝕔 _ => false
  | .lets b e => grounded b ∧ grounded e
  | .lets𝕔 _ _ => false
  | .fix₁ e => grounded e
  | .fix₂ _ => false
  | .ifz₁ c l r => grounded c ∧ grounded l ∧ grounded r
  | .ifz₂ _ _ _ => false

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
  | run _ IH
  | fix₁ _ IH
  | fix₂ _ IH =>
    simp [IH]
  | app₁ _ _ IH₀ IH₁
  | app₂ _ _ IH₀ IH₁
  | binary₁ _ _ _ IH₀ IH₁
  | binary₂ _ _ _ IH₀ IH₁
  | lets _ _ IH₀ IH₁
  | lets𝕔 _ _ IH₀ IH₁ =>
    simp [IH₀, IH₁]
  | ifz₁ _ _ _ IH₀ IH₁ IH₂
  | ifz₂ _ _ _ IH₀ IH₁ IH₂ =>
    simp [IH₀, IH₁, IH₂]

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
  | bvar| fvar| app₂| binary₂| lit| lam𝕔| lets𝕔| fix₂| ifz₂ => simp
  | lam _ IH
  | fix₁ _ IH =>
    simp [IH]
  | app₁ _ _ IH₀ IH₁
  | binary₁ _ _ _ IH₀ IH₁
  | lets _ _ IH₀ IH₁ =>
    simp [IH₀, IH₁]
  | ifz₁ _ _ _ IH₀ IH₁ IH₂ =>
    simp [IH₀, IH₁, IH₂]
  | lift => simp; apply erasable.lift
  | run => simp; apply erasable.run
  | code => simp; apply erasable.code
  | reflect => simp; apply erasable.reflect

lemma grounded.under_opening : ∀ e i x, grounded e ↔ grounded ({i ↦ x} e) :=
  by
  intros e i x
  induction e generalizing i with
  | fvar| app₂| binary₂| lit| lam𝕔| lets𝕔| fix₂| ifz₂| lift| run| code| reflect => simp
  | bvar j =>
    by_cases HEq : j = i
    . simp [if_pos HEq]
    . simp [if_neg HEq]
  | lam _ IH
  | fix₁ _ IH =>
    simp; rw [IH]
  | app₁ _ _ IH₀ IH₁
  | binary₁ _ _ _ IH₀ IH₁
  | lets _ _ IH₀ IH₁ =>
    simp; rw [IH₀, IH₁]
  | ifz₁ _ _ _ IH₀ IH₁ IH₂ =>
    simp; rw [IH₀, IH₁, IH₂]

lemma grounded.under_subst : ∀ e v x, grounded v → grounded e → grounded (subst x v e) :=
  by
  intros e v x
  induction e with
  | bvar| app₂| binary₂| lit| lam𝕔| lets𝕔| fix₂| ifz₂| lift| run| code| reflect => simp
  | fvar y =>
    intros Hv
    by_cases HEq : x = y
    . simp [if_pos HEq, Hv]
    . simp [if_neg HEq]
  | lam _ IH
  | fix₁ _ IH => simp; apply IH
  | app₁ _ _ IH₀ IH₁
  | binary₁ _ _ _ IH₀ IH₁
  | lets _ _ IH₀ IH₁ =>
    simp; intros Hv H₀ H₁; constructor
    apply IH₀; apply Hv; apply H₀
    apply IH₁; apply Hv; apply H₁
  | ifz₁ _ _ _ IH₀ IH₁ IH₂ =>
    simp; intros Hv H₀ H₁ H₂; constructor
    apply IH₀; apply Hv; apply H₀; constructor
    apply IH₁; apply Hv; apply H₁
    apply IH₂; apply Hv; apply H₂

lemma grounded.under_opening_value : ∀ e v i, grounded v → grounded e → grounded (opening i v e) :=
  by
  intros e v i
  induction e generalizing i with
  | fvar| app₂| binary₂| lit| lam𝕔| lets𝕔| fix₂| ifz₂| lift| run| code| reflect => simp
  | bvar j =>
    simp; intros Hv
    by_cases HEq : j = i
    . simp [if_pos HEq, Hv]
    . simp [if_neg HEq]
  | lam _ IH
  | fix₁ _ IH
    => simp; apply IH
  | app₁ _ _ IH₀ IH₁
  | binary₁ _ _ _ IH₀ IH₁
  | lets _ _ IH₀ IH₁ =>
    simp; intros Hv H₀ H₁; constructor
    apply IH₀; apply Hv; apply H₀
    apply IH₁; apply Hv; apply H₁
  | ifz₁ _ _ _ IH₀ IH₁ IH₂ =>
    simp; intros Hv H₀ H₁ H₂; constructor
    apply IH₀; apply Hv; apply H₀; constructor
    apply IH₁; apply Hv; apply H₁
    apply IH₂; apply Hv; apply H₂
