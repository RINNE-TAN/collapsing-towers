import CollapsingTowers.TwoLevelRec.Syntax.Commutative

lemma intros.open_maping𝕔 :
    ∀ x e i,
      closed_at e x →
      ({i ↤ x} subst x (.code (.fvar x)) {i ↦ x} e) = maping𝕔 i e :=
  by
  intros x e i Hclosed
  induction e generalizing i with
  | bvar j => by_cases HEq : j = i; rw [HEq]; simp; simp [if_neg HEq]
  | fvar y => simp at *; by_cases HEq : x = y; omega; rw [if_neg HEq]; simp; apply HEq
  | fix _ IH
  | lift _ IH
  | code _ IH
  | reflect _ IH
  | fix𝕔 _ IH
  | run _ IH =>
    simp at *; apply IH; apply Hclosed
  | app₁ _ _ IH₀ IH₁
  | app₂ _ _ IH₀ IH₁
  | lets _ _ IH₀ IH₁
  | lets𝕔 _ _ IH₀ IH₁ =>
    simp at *; constructor
    apply IH₀; apply Hclosed.left
    apply IH₁; apply Hclosed.right
  | lit => simp

lemma intros.open_maping𝕔2 :
    ∀ x e,
      closed_at e x →
      (
        {1 ↤ x}{0 ↤ x + 1}
        subst x (.code (.fvar x)) (
        subst (x + 1) (.code (.fvar (x + 1)))
        {0 ↦ x + 1}{1 ↦ x}
        e)
      ) = maping𝕔 1 (maping𝕔 0 e) :=
  by
  intros x e Hclosed
  rw [comm.subst_opening]
  all_goals admit

lemma intros.open_subst : ∀ x e v i, closed_at e x → subst x v ({i ↦ x} e) = opening i v e :=
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

lemma intros.open_subst2 :
  ∀ x e v₀ v₁,
    wf_at v₀ x →
    wf_at v₁ x →
    closed_at e x →
    subst x v₁ (subst (x + 1) v₀ ({0 ↦ x + 1}{1 ↦ x} e)) = opening 0 v₀ (opening 1 v₁ e) :=
  by
  intros x e v₀ v₁ Hv₀ Hv₁ He
  rw [intros.open_subst, comm.subst_opening_value, identity.subst, intros.open_subst]
  apply He; apply Hv₀.right; apply Hv₁.left
  apply closed.under_opening; apply He
