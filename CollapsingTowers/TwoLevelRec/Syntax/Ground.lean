import CollapsingTowers.TwoLevelRec.Syntax.SyntacticTrans

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
  | .fix₁ e => grounded e
  | .fix₂ _ => false

lemma erasable.lift : ∀ e₀ e₁, ‖e₀‖ ≠ Expr.lift e₁ :=
  by
  intros e₀ e₁
  induction e₀ <;> simp
  all_goals next IH => apply IH

lemma erasable.run : ∀ e₀ e₁, ‖e₀‖ ≠ Expr.run e₁ :=
  by
  intros e₀ e₁
  induction e₀ <;> simp
  all_goals next IH => apply IH

lemma erasable.code : ∀ e₀ e₁, ‖e₀‖ ≠ Expr.code e₁ :=
  by
  intros e₀ e₁
  induction e₀ <;> simp
  all_goals next IH => apply IH

lemma erasable.reflect : ∀ e₀ e₁, ‖e₀‖ ≠ Expr.reflect e₁ :=
  by
  intros e₀ e₁
  induction e₀ <;> simp
  all_goals next IH => apply IH

lemma grounded_iff_erase_identity : ∀ e, grounded e ↔ ‖e‖ = e :=
  by
  intros e
  induction e <;> simp
  case lam IH => apply IH
  case app₁ IH₀ IH₁ => rw [IH₀, IH₁]
  case lift => apply erasable.lift
  case run => apply erasable.run
  case code => apply erasable.code
  case reflect => apply erasable.reflect
  case lets IH₀ IH₁ => rw [IH₀, IH₁]
  case fix₁ IH => apply IH
