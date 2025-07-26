import CollapsingTowers.TwoLvLBasic.Syntax.Opening
import CollapsingTowers.TwoLvLBasic.Syntax.Closing
import CollapsingTowers.TwoLvLBasic.Syntax.Shift
import CollapsingTowers.TwoLvLBasic.Syntax.Lc
import CollapsingTowers.TwoLvLBasic.Syntax.Closed

lemma comm.shiftl_opening :
    ∀ x y e n i, x ≤ y → ({x << n}{i ↦ y} e) = ({i ↦ y + n}{x << n} e) :=
  by
  intros x y e n i HLe
  induction e generalizing i with
  | bvar j =>
    by_cases HEq : j = i
    . rw [HEq]; simp; omega
    . simp; rw [if_neg HEq]; rw [if_neg HEq]; rfl
  | fvar z =>
    by_cases HLe : x ≤ z
    . simp; rw [if_pos HLe]; rfl
    . simp; rw [if_neg HLe]; rfl
  | app₁ _ _ IH₀ IH₁
  | app₂ _ _ IH₀ IH₁
  | lets _ _ IH₀ IH₁
  | lets𝕔 _ _ IH₀ IH₁ =>
    simp; constructor; apply IH₀; apply IH₁
  | lit => simp
  | lam _ IH
  | lift _ IH
  | lam𝕔 _ IH
  | code _ IH
  | reflect _ IH
  | run _ IH =>
    simp; apply IH
