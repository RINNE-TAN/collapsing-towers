import CollapsingTowers.TwoLevelFinal.Syntax.LocallyNameless

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
  | lit| unit| loc => simp
  | lam _ IH
  | lift _ IH
  | code _ IH
  | reflect _ IH
  | lam𝕔 _ IH
  | run _ IH
  | alloc₁ _ IH
  | alloc₂ _ IH
  | load₁ _ IH
  | load₂ _ IH
  | fix₁ _ IH
  | fix₂ _ IH =>
    simp; apply IH; apply Hclosed
  | app₁ _ _ IH₀ IH₁
  | app₂ _ _ IH₀ IH₁
  | lets _ _ IH₀ IH₁
  | lets𝕔 _ _ IH₀ IH₁
  | store₁ _ _ IH₀ IH₁
  | store₂ _ _ IH₀ IH₁ =>
    simp; constructor
    apply IH₀; apply Hclosed.left
    apply IH₁; apply Hclosed.right
  | ifz₁ _ _ _ IH₀ IH₁ IH₂
  | ifz₂ _ _ _ IH₀ IH₁ IH₂ =>
    simp; constructor
    apply IH₀; apply Hclosed.left; constructor
    apply IH₁; apply Hclosed.right.left
    apply IH₂; apply Hclosed.right.right

lemma intro.subst : ∀ x e v i, closed_at e x → subst x v (opening i (.fvar x) e) = opening i v e :=
  by
  intros _ e _ i Hclosed
  induction e generalizing i with
  | bvar j =>
    by_cases HEq : j = i
    . simp [HEq]
    . simp [if_neg HEq]
  | fvar => simp at *; omega
  | lit| unit| loc => simp
  | lam _ IH
  | lift _ IH
  | code _ IH
  | reflect _ IH
  | lam𝕔 _ IH
  | run _ IH
  | alloc₁ _ IH
  | alloc₂ _ IH
  | load₁ _ IH
  | load₂ _ IH
  | fix₁ _ IH
  | fix₂ _ IH =>
    simp; apply IH; apply Hclosed
  | app₁ _ _ IH₀ IH₁
  | app₂ _ _ IH₀ IH₁
  | lets _ _ IH₀ IH₁
  | lets𝕔 _ _ IH₀ IH₁
  | store₁ _ _ IH₀ IH₁
  | store₂ _ _ IH₀ IH₁ =>
    simp; constructor
    apply IH₀; apply Hclosed.left
    apply IH₁; apply Hclosed.right
  | ifz₁ _ _ _ IH₀ IH₁ IH₂
  | ifz₂ _ _ _ IH₀ IH₁ IH₂ =>
    simp; constructor
    apply IH₀; apply Hclosed.left; constructor
    apply IH₁; apply Hclosed.right.left
    apply IH₂; apply Hclosed.right.right
