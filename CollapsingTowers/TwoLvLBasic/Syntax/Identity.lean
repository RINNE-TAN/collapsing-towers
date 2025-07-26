import CollapsingTowers.TwoLvLBasic.Syntax.Opening
import CollapsingTowers.TwoLvLBasic.Syntax.Closing
import CollapsingTowers.TwoLvLBasic.Syntax.Lc

lemma identity.opening_closing : ∀ i e x, lc_at e i → ({i ↦ x}{i ↤ x}e) = e :=
  by
  intros i e x Hlc
  induction e generalizing i with
  | bvar j =>
    simp
    intro HEq
    rw [HEq] at Hlc
    simp at Hlc
  | fvar y =>
    by_cases HEq : x = y
    . simp [if_pos HEq]
      apply HEq
    . simp [if_neg HEq]
  | lam _ IH
  | lift _ IH
  | lam𝕔 _ IH
  | code _ IH
  | reflect _ IH
  | run _ IH =>
    simp; apply IH; apply Hlc
  | app₁ _ _ IH₀ IH₁
  | app₂ _ _ IH₀ IH₁
  | lets _ _ IH₀ IH₁
  | lets𝕔 _ _ IH₀ IH₁ =>
    simp; constructor
    apply IH₀; apply Hlc.left
    apply IH₁; apply Hlc.right
  | lit => rfl
