import CollapsingTowers.TwoLvLBasic.Syntax.Identity

lemma comm.subst_opening :
    ∀ x y v e i, x ≠ y → lc v → subst x v ({i ↦ y} e) = ({i ↦ y} subst x v e) :=
  by
  intro x y v e i HNe Hlc
  induction e generalizing i with
  | bvar j =>
    by_cases HEq : j = i
    . simp [if_pos HEq]; omega
    . simp [if_neg HEq]
  | fvar z =>
    by_cases HEq : x = z
    . simp; rw [if_pos HEq]; rw [identity.opening]
      apply lc.inc; apply Hlc; omega
    . simp; rw [if_neg HEq]; simp
  | app₁ _ _ IH₀ IH₁
  | app₂ _ _ IH₀ IH₁ =>
    simp; constructor
    apply IH₀
    apply IH₁
  | lets _ _ IH₀ IH₁
  | lets𝕔 _ _ IH₀ IH₁ =>
    simp; constructor
    apply IH₀
    apply IH₁
  | code _ IH
  | reflect _ IH
  | run _ IH =>
    simp; apply IH
  | lit => simp
  | lam _ IH
  | lift _ IH
  | lam𝕔 _ IH =>
    simp; apply IH

lemma comm.shiftl_opening :
    ∀ x y e n i, x ≤ y → (shiftl_at x n {i ↦ y} e) = ({i ↦ y + n} shiftl_at x n e) :=
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

lemma comm.shiftr_opening :
    ∀ x y e i, x < y → shiftr_at x (opening i (.fvar y) e) = opening i (.fvar (y - 1)) (shiftr_at x e) :=
  by
  intros x y e i HLe
  induction e generalizing i with
  | bvar j =>
    by_cases HEq : j = i
    . rw [HEq]; simp; omega
    . simp; rw [if_neg HEq, if_neg HEq]; simp
  | fvar z =>
    by_cases HLe : x < z
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
