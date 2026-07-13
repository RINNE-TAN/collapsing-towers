import Instar.TwoLevelMut.Syntax.LocallyNameless

lemma identity.opening : ∀ e v i, lc_at e i → (opening i v e) = e :=
  by
  intros e v i Hlc
  induction e generalizing i with
  | fvar| lit| unit| loc => simp
  | bvar => simp at *; omega
  | lift _ IH
  | code _ IH
  | reflect _ IH
  | run _ IH
  | lam _ IH
  | lam𝕔 _ IH
  | alloc₁ _ IH
  | alloc₂ _ IH
  | load₁ _ IH
  | load₂ _ IH =>
    simp; apply IH; apply Hlc
  | app₁ _ _ IH₀ IH₁
  | app₂ _ _ IH₀ IH₁
  | lets _ _ IH₀ IH₁
  | lets𝕔 _ _ IH₀ IH₁
  | store₁ _ _ IH₀ IH₁
  | store₂ _ _ IH₀ IH₁ =>
    simp; constructor
    apply IH₀; apply Hlc.left
    apply IH₁; apply Hlc.right

lemma identity.opening_closing : ∀ i e x, lc_at e i → ({i ↦ x}{i ↤ x} e) = e :=
  by
  intros i e x Hlc
  induction e generalizing i with
  | bvar j =>
    simp at *; omega
  | fvar y =>
    by_cases HEq : x = y
    . simp [if_pos HEq]; omega
    . simp [if_neg HEq]
  | lit| unit| loc => rfl
  | lam _ IH
  | lift _ IH
  | lam𝕔 _ IH
  | alloc₁ _ IH
  | alloc₂ _ IH
  | load₁ _ IH
  | load₂ _ IH
  | code _ IH
  | reflect _ IH
  | run _ IH =>
    simp; apply IH; apply Hlc
  | app₁ _ _ IH₀ IH₁
  | app₂ _ _ IH₀ IH₁
  | lets _ _ IH₀ IH₁
  | lets𝕔 _ _ IH₀ IH₁
  | store₁ _ _ IH₀ IH₁
  | store₂ _ _ IH₀ IH₁ =>
    simp; constructor
    apply IH₀; apply Hlc.left
    apply IH₁; apply Hlc.right

lemma identity.closing_opening : ∀ i e x, closed_at e x → ({i ↤ x}{i ↦ x} e) = e :=
  by
  intros i e x Hclosed
  induction e generalizing i with
  | bvar j =>
    by_cases HEq : j = i
    . simp [if_pos HEq]; omega
    . simp [if_neg HEq]
  | fvar => simp at *; omega
  | lit| unit| loc => rfl
  | lam _ IH
  | lift _ IH
  | lam𝕔 _ IH
  | alloc₁ _ IH
  | alloc₂ _ IH
  | load₁ _ IH
  | load₂ _ IH
  | code _ IH
  | reflect _ IH
  | run _ IH =>
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

lemma identity.shiftl :
    ∀ x e n, closed_at e x → shiftl x n e = e :=
  by
  intros x e n
  induction e with
  | bvar| lit| unit| loc => simp
  | fvar => simp; omega
  | lam _ IH
  | lift _ IH
  | lam𝕔 _ IH
  | alloc₁ _ IH
  | alloc₂ _ IH
  | load₁ _ IH
  | load₂ _ IH
  | code _ IH
  | reflect _ IH
  | run _ IH =>
    simp; apply IH
  | app₁ _ _ IH₀ IH₁
  | app₂ _ _ IH₀ IH₁
  | lets _ _ IH₀ IH₁
  | lets𝕔 _ _ IH₀ IH₁
  | store₁ _ _ IH₀ IH₁
  | store₂ _ _ IH₀ IH₁ =>
    intro Hclosed; simp; constructor
    apply IH₀; apply Hclosed.left
    apply IH₁; apply Hclosed.right

lemma identity.shiftr :
    ∀ x e, closed_at e (x + 1) → shiftr x e = e :=
  by
  intros x e
  induction e with
  | bvar| lit| unit| loc => simp
  | fvar y => simp; omega
  | lam _ IH
  | lift _ IH
  | lam𝕔 _ IH
  | alloc₁ _ IH
  | alloc₂ _ IH
  | load₁ _ IH
  | load₂ _ IH
  | code _ IH
  | reflect _ IH
  | run _ IH =>
    simp; apply IH
  | app₁ _ _ IH₀ IH₁
  | app₂ _ _ IH₀ IH₁
  | lets _ _ IH₀ IH₁
  | lets𝕔 _ _ IH₀ IH₁
  | store₁ _ _ IH₀ IH₁
  | store₂ _ _ IH₀ IH₁ =>
    intro Hclosed; simp; constructor
    apply IH₀; apply Hclosed.left
    apply IH₁; apply Hclosed.right

lemma identity.subst : ∀ x e v, closed_at e x → subst x v e = e :=
  by
  intros x e v Hclosed
  induction e with
  | bvar| lit| unit| loc => simp
  | fvar => simp at *; omega
  | lam _ IH
  | lift _ IH
  | lam𝕔 _ IH
  | alloc₁ _ IH
  | alloc₂ _ IH
  | load₁ _ IH
  | load₂ _ IH
  | code _ IH
  | reflect _ IH
  | run _ IH =>
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

lemma identity.msubst : ∀ γ e, closed e → msubst γ e = e :=
  by
  intro γ e Hclosed
  induction γ generalizing e
  case nil => rfl
  case cons IH =>
    simp; rw [IH, identity.subst]
    apply closed.inc; apply Hclosed; omega
    rw [identity.subst]; apply Hclosed
    apply closed.inc; apply Hclosed; omega

lemma identity.erase_codify : ∀ i e, ⎸codify i e⎹ = ⎸e⎹ :=
  by
  intros i e
  induction e generalizing i with
  | bvar j =>
    by_cases HEq : j = i
    . simp [if_pos HEq]; omega
    . simp [if_neg HEq]
  | fvar| lit| unit| loc => simp
  | lam _ IH
  | lift _ IH
  | code _ IH
  | reflect _ IH
  | lam𝕔 _ IH
  | alloc₁ _ IH
  | alloc₂ _ IH
  | load₁ _ IH
  | load₂ _ IH
  | run _ IH =>
    simp [IH]
  | app₁ _ _ IH₀ IH₁
  | app₂ _ _ IH₀ IH₁
  | lets _ _ IH₀ IH₁
  | lets𝕔 _ _ IH₀ IH₁
  | store₁ _ _ IH₀ IH₁
  | store₂ _ _ IH₀ IH₁ =>
    simp [IH₀, IH₁]
