import CollapsingTowers.TwoLevelRec.Syntax.Closedness

lemma identity.shiftl :
    ∀ x e n, closed_at e x → shiftl_at x n e = e :=
  by
  intros x e n
  induction e with
  | bvar j => simp
  | fvar y => simp; omega
  | app₁ _ _ IH₀ IH₁
  | app₂ _ _ IH₀ IH₁
  | lets _ _ IH₀ IH₁
  | lets𝕔 _ _ IH₀ IH₁ =>
    intro Hclosed; simp; constructor
    apply IH₀; apply Hclosed.left
    apply IH₁; apply Hclosed.right
  | lit => simp
  | fix _ IH
  | lift _ IH
  | fix𝕔 _ IH
  | code _ IH
  | reflect _ IH
  | run _ IH =>
    simp; apply IH
