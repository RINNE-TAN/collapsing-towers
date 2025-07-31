import CollapsingTowers.TwoLevelRec.Syntax.Identity

lemma comm.subst_opening : ∀ x y v e i, x ≠ y → lc v → subst x v ({i ↦ y} e) = ({i ↦ y} subst x v e) :=
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
  | fix _ IH
  | lift _ IH
  | fix𝕔 _ IH =>
    simp; apply IH

lemma comm.subst_opening_value :
    ∀ x v₀ v₁ e i, lc_at v₀ i → subst x v₀ (opening i v₁ e) = opening i (subst x v₀ v₁) (subst x v₀ e) :=
  by
  intro x v₀ v₁ e i Hlc
  induction e generalizing i with
  | bvar j =>
    by_cases HEq : j = i
    . simp; rw [if_pos HEq]; simp; omega
    . simp; rw [if_neg HEq, if_neg HEq]; simp
  | fvar z =>
    by_cases HEq : x = z
    . simp; rw [if_pos HEq]; rw [identity.opening]; apply Hlc
    . simp; rw [if_neg HEq]; simp
  | app₁ _ _ IH₀ IH₁
  | app₂ _ _ IH₀ IH₁ =>
    simp; constructor
    apply IH₀; apply Hlc
    apply IH₁; apply Hlc
  | lets _ _ IH₀ IH₁
  | lets𝕔 _ _ IH₀ IH₁ =>
    simp; constructor
    apply IH₀; apply Hlc
    apply IH₁; apply lc.inc; apply Hlc; omega
  | code _ IH
  | reflect _ IH
  | run _ IH =>
    simp; apply IH; apply Hlc
  | lit => simp
  | fix _ IH
  | lift _ IH
  | fix𝕔 _ IH =>
    simp; apply IH; apply lc.inc; apply Hlc; omega

lemma comm.shiftl_opening : ∀ x y e n i, x ≤ y → (shiftl_at x n {i ↦ y} e) = ({i ↦ y + n} shiftl_at x n e) :=
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
  | fix _ IH
  | lift _ IH
  | fix𝕔 _ IH
  | code _ IH
  | reflect _ IH
  | run _ IH =>
    simp; apply IH

lemma comm.shiftr_opening : ∀ x y e i, x < y → shiftr_at x (opening i (.fvar y) e) = opening i (.fvar (y - 1)) (shiftr_at x e) :=
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
  | fix _ IH
  | lift _ IH
  | fix𝕔 _ IH
  | code _ IH
  | reflect _ IH
  | run _ IH =>
    simp; apply IH

lemma comm.erase_opening : ∀ i x e, ‖{i ↦ x} e‖ = {i ↦ x} ‖e‖ :=
  by
  intros i x e
  induction e generalizing i with
  | bvar j =>
    by_cases HEq : j = i
    . simp [if_pos HEq]
    . simp [if_neg HEq]
  | fvar| lit => simp
  | app₁ _ _ IH₀ IH₁
  | app₂ _ _ IH₀ IH₁
  | lets _ _ IH₀ IH₁
  | lets𝕔 _ _ IH₀ IH₁ =>
    simp; constructor
    apply IH₀; apply IH₁
  | code _ IH
  | reflect _ IH
  | lift _ IH
  | run _ IH
  | fix _ IH
  | fix𝕔 _ IH => simp; apply IH

lemma comm.erase_opening_subst : ∀ i v e, ‖opening i v e‖ = opening i ‖v‖ ‖e‖ :=
  by
  intros i v e
  induction e generalizing i with
  | bvar j =>
    by_cases HEq : j = i
    . simp [if_pos HEq]
    . simp [if_neg HEq]
  | fvar| lit => simp
  | app₁ _ _ IH₀ IH₁
  | app₂ _ _ IH₀ IH₁
  | lets _ _ IH₀ IH₁
  | lets𝕔 _ _ IH₀ IH₁ =>
    simp; constructor
    apply IH₀; apply IH₁
  | code _ IH
  | reflect _ IH
  | lift _ IH
  | run _ IH
  | fix _ IH
  | fix𝕔 _ IH => simp; apply IH

lemma comm.multi_subst_opening : ∀ γ x e i, x ≥ γ.length → multi_wf γ → multi_subst γ ({i ↦ x} e) = {i ↦ x} (multi_subst γ e) :=
  by
  intros γ x e i HGe Hγ
  induction γ generalizing e
  case nil => rfl
  case cons IH =>
    simp at *
    rw [comm.subst_opening, IH]
    omega; apply Hγ.right; omega
    apply lc.inc; apply Hγ.left.left; omega

lemma comm.multi_subst_opening_value :
    ∀ γ v e i, multi_wf γ → multi_subst γ (opening i v e) = opening i (multi_subst γ v) (multi_subst γ e) :=
    by
    intros γ v e i Hγ
    induction γ generalizing e v
    case nil => rfl
    case cons IH =>
      rw [multi_subst, comm.subst_opening_value, IH]
      rfl; apply Hγ.right
      apply lc.inc; apply Hγ.left.left; omega

lemma comm.subst_subst : ∀ x y v₀ v₁ e, x ≠ y → closed v₀ → closed v₁ → subst x v₀ (subst y v₁ e) = subst y v₁ (subst x v₀ e) :=
  by
  intro x y v₀ v₁ e HNe Hclose₀ Hclose₁
  induction e with
  | bvar j => simp
  | fvar z =>
    by_cases HEqx : x = z
    . simp [if_pos HEqx]
      by_cases HEqy : y = z
      . simp [if_pos HEqy]
        omega
      . simp [if_neg HEqy, if_pos HEqx]
        rw [identity.subst]
        apply closed.inc; apply Hclose₀; omega
    . simp [if_neg HEqx]
      by_cases HEqy : y = z
      . simp [if_pos HEqy]
        rw [identity.subst]
        apply closed.inc; apply Hclose₁; omega
      . simp [if_neg HEqy, if_neg HEqx]
  | app₁ _ _ IH₀ IH₁
  | app₂ _ _ IH₀ IH₁
  | lets _ _ IH₀ IH₁
  | lets𝕔 _ _ IH₀ IH₁ =>
    simp; constructor
    apply IH₀; apply IH₁
  | fix _ IH
  | lift _ IH
  | fix𝕔 _ IH
  | code _ IH
  | reflect _ IH
  | run _ IH =>
    simp; apply IH
  | lit => simp

lemma comm.multi_subst_subst : ∀ x γ v e, x ≥ γ.length → closed v →  multi_wf γ → subst x v (multi_subst γ e) = multi_subst γ (subst x v e) :=
  by
  intro x γ v e HGe Hclose Hγ
  induction γ generalizing e
  case nil => simp
  case cons IH =>
    simp at HGe
    rw [multi_subst, multi_subst, IH, comm.subst_subst]
    omega; apply Hclose; apply Hγ.left.right
    omega; apply Hγ.right
