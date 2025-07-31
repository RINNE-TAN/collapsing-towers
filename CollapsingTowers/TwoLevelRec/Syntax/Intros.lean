import CollapsingTowers.TwoLevelRec.Syntax.Closedness

lemma intros.maping𝕔 :
    ∀ x e i,
      closed_at e x →
      ({i ↤ x} subst x (.code (.fvar x)) {i ↦ x} e) = maping𝕔 i e :=
  by
  intros x e i Hclose
  induction e generalizing i with
  | bvar j => by_cases HEq : j = i; rw [HEq]; simp; simp [if_neg HEq]
  | fvar y => simp at *; by_cases HEq : x = y; omega; rw [if_neg HEq]; simp; apply HEq
  | fix _ IH
  | lift _ IH
  | code _ IH
  | reflect _ IH
  | fix𝕔 _ IH
  | run _ IH =>
    simp at *; apply IH; apply Hclose
  | app₁ _ _ IH₀ IH₁
  | app₂ _ _ IH₀ IH₁
  | lets _ _ IH₀ IH₁
  | lets𝕔 _ _ IH₀ IH₁ =>
    simp at *; constructor
    apply IH₀; apply Hclose.left
    apply IH₁; apply Hclose.right
  | lit => simp

lemma intros.subst : ∀ x e v i, closed_at e x → subst x v ({i ↦ x} e) = opening i v e :=
  by
  intros _ e _ i Hclosed
  induction e generalizing i with
  | bvar j =>
    by_cases HEq : j = i
    . simp [HEq]
    . simp [if_neg HEq]
  | fvar y =>
    simp at *; omega
  | fix _ IH
  | lift _ IH
  | code _ IH
  | reflect _ IH
  | fix𝕔 _ IH
  | run _ IH =>
    simp; apply IH; apply Hclosed
  | app₁ _ _ IH₀ IH₁
  | app₂ _ _ IH₀ IH₁
  | lets _ _ IH₀ IH₁
  | lets𝕔 _ _ IH₀ IH₁ =>
    simp; constructor
    apply IH₀; apply Hclosed.left
    apply IH₁; apply Hclosed.right
  | lit => simp
