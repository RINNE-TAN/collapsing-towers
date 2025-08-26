import CollapsingTowers.TwoLevelBasic.Syntax.LocallyNameless

lemma intro.codify : ∀ x e i, closed_at e x → ({i ↤ x} subst x (.code (.fvar x)) ({i ↦ x} e)) = codify i e :=
  by
  intros x e i Hclosed
  induction e generalizing i with
  | bvar j =>
    by_cases HEq : j = i
    . simp [HEq]
    . simp [if_neg HEq]
  | fvar y =>
    by_cases HEq : x = y
    . simp at *; omega
    . simp [if_neg HEq]
  | lit => simp
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
  | lets𝕔 _ _ IH₀ IH₁ =>
    simp; constructor
    apply IH₀; apply Hclosed.left
    apply IH₁; apply Hclosed.right

lemma intro.subst : ∀ x e v i, closed_at e x → subst x v (opening i (.fvar x) e) = opening i v e :=
  by
  intros _ e _ i Hclosed
  induction e generalizing i with
  | bvar j =>
    by_cases HEq : j = i
    . simp [HEq]
    . simp [if_neg HEq]
  | fvar => simp at *; omega
  | lit => simp
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
  | lets𝕔 _ _ IH₀ IH₁ =>
    simp; constructor
    apply IH₀; apply Hclosed.left
    apply IH₁; apply Hclosed.right
