import CollapsingTowers.TwoLevelRec.Syntax.Closedness

lemma identity.opening : ∀ e v i, lc_at e i → (opening i v e) = e :=
  by
  intros e v i Hlc
  induction e generalizing i with
  | fvar y => simp
  | bvar j => simp at *; omega
  | lift _ IH
  | code _ IH
  | reflect _ IH
  | run _ IH
  | fix _ IH
  | fix𝕔 _ IH =>
    simp; apply IH; apply Hlc
  | app₁ _ _ IH₀ IH₁
  | app₂ _ _ IH₀ IH₁
  | lets _ _ IH₀ IH₁
  | lets𝕔 _ _ IH₀ IH₁ =>
    simp; constructor
    apply IH₀; apply Hlc.left
    apply IH₁; apply Hlc.right
  | lit => simp

lemma identity.opening_closing : ∀ i e x, lc_at e i → ({i ↦ x}{i ↤ x} e) = e :=
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
  | fix _ IH
  | lift _ IH
  | fix𝕔 _ IH
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

lemma identity.closing_opening : ∀ i e x, closed_at e x → ({i ↤ x}{i ↦ x} e) = e :=
  by
  intros i e x Hclosed
  induction e generalizing i with
  | bvar j =>
    by_cases HEq : j = i
    . simp; rw [if_pos HEq]; simp; omega
    . simp; rw [if_neg HEq]; simp
  | fvar y => simp at *; omega
  | fix _ IH
  | lift _ IH
  | fix𝕔 _ IH
  | code _ IH
  | reflect _ IH
  | run _ IH =>
    simp; apply IH; apply Hclosed
  | app₁ _ _ IH₀ IH₁
  | app₂ _ _ IH₀ IH₁
  | lets _ _ IH₀ IH₁
  | lets𝕔 _ _ IH₀ IH₁ =>
    simp; constructor
    apply IH₀; apply Hclosed.left
    apply IH₁; apply Hclosed.right
  | lit => rfl

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

lemma identity.shiftr :
    ∀ x e, closed_at e (x + 1) → shiftr_at x e = e :=
  by
  intros x e
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

lemma identity.subst : ∀ x e v, closed_at e x → subst x v e = e :=
  by
  intros x e v He
  induction e with
  | bvar => simp
  | fvar => simp at *; omega
  | fix _ IH
  | lift _ IH
  | fix𝕔 _ IH
  | code _ IH
  | reflect _ IH
  | run _ IH =>
    simp; apply IH; apply He
  | app₁ _ _ IH₀ IH₁
  | app₂ _ _ IH₀ IH₁ =>
    simp; constructor
    apply IH₀; apply He.left
    apply IH₁; apply He.right
  | lets _ _ IHb IH
  | lets𝕔 _ _ IHb IH =>
    simp; constructor
    apply IHb; apply He.left
    apply IH; apply He.right
  | lit => simp

lemma identity.multi_subst : ∀ γ e, closed e → multi_subst γ e = e :=
  by
  intro γ e Hclose
  induction γ generalizing e
  case nil => rfl
  case cons IH =>
    simp; rw [IH, identity.subst]
    apply closed.inc; apply Hclose; omega
    rw [identity.subst]; apply Hclose
    apply closed.inc; apply Hclose; omega

lemma identity.erase_erase : ∀ e, ‖‖e‖‖ = ‖e‖ :=
  by
  intros e
  induction e with
  | bvar j => rfl
  | fvar y => rfl
  | fix _ IH
  | lift _ IH
  | code _ IH
  | reflect _ IH
  | fix𝕔 _ IH
  | run _ IH =>
    simp; apply IH
  | app₁ _ _ IH₀ IH₁
  | app₂ _ _ IH₀ IH₁
  | lets _ _ IH₀ IH₁
  | lets𝕔 _ _ IH₀ IH₁ =>
    simp; constructor
    apply IH₀; apply IH₁
  | lit => rfl

lemma identity.erase_maping𝕔 : ∀ i e, ‖maping𝕔 i e‖ = ‖e‖ :=
  by
  intros i e
  induction e generalizing i with
  | bvar j => by_cases HEq : j = i; rw [HEq]; simp; simp [if_neg HEq]
  | fvar y => simp
  | fix _ IH
  | lift _ IH
  | code _ IH
  | reflect _ IH
  | fix𝕔 _ IH
  | run _ IH =>
    simp; apply IH
  | app₁ _ _ IH₀ IH₁
  | app₂ _ _ IH₀ IH₁
  | lets _ _ IH₀ IH₁
  | lets𝕔 _ _ IH₀ IH₁ =>
    simp; constructor
    apply IH₀; apply IH₁
  | lit => simp
