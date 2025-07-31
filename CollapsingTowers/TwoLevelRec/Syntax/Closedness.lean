import CollapsingTowers.TwoLevelRec.Syntax.Fv

-- closedness condition for free variables
@[simp]
def closed_at (e : Expr) (x : ℕ) : Prop :=
  match e with
  | .bvar _ => true
  | .fvar y => y < x
  | .fix e => closed_at e x
  | .lift e => closed_at e x
  | .app₁ f arg => closed_at f x ∧ closed_at arg x
  | .app₂ f arg => closed_at f x ∧ closed_at arg x
  | .lit _ => true
  | .run e => closed_at e x
  | .code e => closed_at e x
  | .reflect e => closed_at e x
  | .fix𝕔 e => closed_at e x
  | .lets b e => closed_at b x ∧ closed_at e x
  | .lets𝕔 b e => closed_at b x ∧ closed_at e x

@[simp]
def closed e := closed_at e 0

-- closedness condition for bound variables
@[simp]
def lc_at (e : Expr) (i : ℕ) : Prop :=
  match e with
  | .bvar j => j < i
  | .fvar _ => true
  | .fix e => lc_at e (i + 2)
  | .lift e => lc_at e i
  | .app₁ f arg => lc_at f i ∧ lc_at arg i
  | .app₂ f arg => lc_at f i ∧ lc_at arg i
  | .lit _ => true
  | .run e => lc_at e i
  | .code e => lc_at e i
  | .reflect e => lc_at e i
  | .fix𝕔 e => lc_at e (i + 2)
  | .lets b e => lc_at b i ∧ lc_at e (i + 1)
  | .lets𝕔 b e => lc_at b i ∧ lc_at e (i + 1)

@[simp]
def lc e := lc_at e 0

@[simp]
def wf_at (e : Expr) (x : ℕ) : Prop := lc e ∧ closed_at e x

@[simp]
def wf (e : Expr) : Prop := wf_at e 0

@[simp]
def multi_wf : Subst → Prop
  | [] => true
  | v :: γ => wf v ∧ multi_wf γ

lemma closed.fv_not_in_dec :
  ∀ e x,
    closed_at e (x + 1) →
    x ∉ fv e →
    closed_at e x :=
  by
  intros e x Hclosedd HFv
  induction e with
  | bvar j => simp
  | fvar y => simp at *; omega
  | lit => simp
  | lift _ IH
  | code _ IH
  | reflect _ IH
  | run _ IH
  | fix _ IH
  | fix𝕔 _ IH =>
    apply IH; apply Hclosedd; apply HFv
  | app₁ _ _ IH₀ IH₁
  | app₂ _ _ IH₀ IH₁
  | lets _ _ IH₀ IH₁
  | lets𝕔 _ _ IH₀ IH₁ =>
    simp at HFv; constructor
    apply IH₀; apply Hclosedd.left; apply HFv.left
    apply IH₁; apply Hclosedd.right; apply HFv.right

lemma closed.inc : ∀ x y e, closed_at e x → x ≤ y → closed_at e y :=
  by
  intros x y e Hclosed Hxy
  induction e with
  | bvar j => simp
  | fvar z => simp at *; omega
  | app₁ _ _ IH₀ IH₁
  | app₂ _ _ IH₀ IH₁
  | lets _ _ IH₀ IH₁
  | lets𝕔 _ _ IH₀ IH₁ =>
    simp; constructor
    apply IH₀; apply Hclosed.left
    apply IH₁; apply Hclosed.right
  | lit => simp
  | fix _ IH
  | lift _ IH
  | fix𝕔 _ IH
  | code _ IH
  | reflect _ IH
  | run _ IH =>
    simp; apply IH; apply Hclosed

lemma closed.under_closing : ∀ e x i, closed_at e (x + 1) ↔ closed_at ({i ↤ x} e) x :=
  by
  intros e x i
  induction e generalizing i with
  | fvar y =>
    by_cases HEq : x = y
    . rw [HEq]; simp
    . simp; rw [if_neg HEq]; simp; omega
  | bvar => simp
  | fix _ IH
  | lift _ IH
  | fix𝕔 _ IH
  | code _ IH
  | reflect _ IH
  | run _ IH =>
    apply IH
  | app₁ _ _ IH₀ IH₁
  | app₂ _ _ IH₀ IH₁
  | lets _ _ IH₀ IH₁
  | lets𝕔 _ _ IH₀ IH₁ =>
    constructor
    . intro Hclosed; constructor
      apply (IH₀ _).mp; apply Hclosed.left
      apply (IH₁ _).mp; apply Hclosed.right
    . intro Hclosed; constructor
      apply (IH₀ _).mpr; apply Hclosed.left
      apply (IH₁ _).mpr; apply Hclosed.right
  | lit => simp

lemma closed.under_opening : ∀ e x i, closed_at e x → closed_at ({i ↦ x} e) (x + 1) :=
  by
  intros e x i
  induction e generalizing i with
  | fvar y => simp; omega
  | bvar j =>
    by_cases HEq : j = i
    . rw [HEq]; simp
    . simp; rw [if_neg HEq]; simp
  | fix _ IH
  | lift _ IH
  | fix𝕔 _ IH
  | code _ IH
  | reflect _ IH
  | run _ IH =>
    apply IH
  | app₁ _ _ IH₀ IH₁
  | app₂ _ _ IH₀ IH₁
  | lets _ _ IH₀ IH₁
  | lets𝕔 _ _ IH₀ IH₁ =>
    intro Hclosed; constructor
    apply IH₀; apply Hclosed.left
    apply IH₁; apply Hclosed.right
  | lit => simp

lemma closed.under_shiftl :
    ∀ x y e n, closed_at e x → closed_at (shiftl_at y n e) (x + n) :=
  by
  intros x y e n Hclosed
  induction e with
  | bvar j => simp
  | fvar z =>
    by_cases HLe : y ≤ z
    . simp; rw [if_pos HLe]; simp; apply Hclosed
    . simp; rw [if_neg HLe]; simp at *; omega
  | app₁ _ _ IH₀ IH₁
  | app₂ _ _ IH₀ IH₁
  | lets _ _ IH₀ IH₁
  | lets𝕔 _ _ IH₀ IH₁ =>
    simp; constructor
    apply IH₀; apply Hclosed.left
    apply IH₁; apply Hclosed.right
  | lit => simp
  | fix _ IH
  | lift _ IH
  | fix𝕔 _ IH
  | code _ IH
  | reflect _ IH
  | run _ IH =>
    simp; apply IH; apply Hclosed

lemma closed.under_subst : ∀ x e v y, closed_at v y → closed_at e y → closed_at (subst x v e) y :=
  by
  intros x e v y Hv He
  induction e generalizing y with
  | bvar => apply He
  | fvar z =>
    by_cases HEq : x = z
    . rw [HEq]; simp; apply Hv
    . simp; rw [if_neg HEq]; apply He
  | fix _ IH
  | lift _ IH
  | fix𝕔 _ IH =>
    apply IH; apply Hv; apply He
  | app₁ _ _ IH₀ IH₁
  | app₂ _ _ IH₀ IH₁
  | lets _ _ IH₀ IH₁
  | lets𝕔 _ _ IH₀ IH₁ =>
    constructor
    apply IH₀; apply Hv; apply He.left
    apply IH₁; apply Hv; apply He.right
  | code _ IH
  | reflect _ IH
  | run _ IH =>
    simp; apply IH; apply Hv; apply He
  | lit => simp

lemma closed.under_subst_dec : ∀ x e v, closed_at v x → closed_at e (x + 1) → closed_at (subst x v e) x :=
  by
  intros x e v Hv He
  induction e with
  | bvar => apply He
  | fvar z =>
    by_cases HEq : x = z
    . rw [← HEq]; simp; apply Hv
    . simp; rw [if_neg HEq]; simp at *; omega
  | fix _ IH
  | lift _ IH
  | fix𝕔 _ IH =>
    apply IH; apply He
  | app₁ _ _ IH₀ IH₁
  | app₂ _ _ IH₀ IH₁
  | lets _ _ IH₀ IH₁
  | lets𝕔 _ _ IH₀ IH₁ =>
    constructor
    apply IH₀; apply He.left
    apply IH₁; apply He.right
  | code _ IH
  | reflect _ IH
  | run _ IH =>
    simp; apply IH; apply He
  | lit => simp

lemma closed.under_shiftr : ∀ x e, closed_at e x → closed_at (shiftr_at x e) x :=
  by
  intros x e Hclosed
  induction e with
  | bvar j => simp
  | fvar z =>
    by_cases Hxz : x < z
    . simp; rw [if_pos Hxz]; simp at *; omega
    . simp; rw [if_neg Hxz]; simp at *; omega
  | app₁ _ _ IH₀ IH₁
  | app₂ _ _ IH₀ IH₁
  | lets _ _ IH₀ IH₁
  | lets𝕔 _ _ IH₀ IH₁ =>
    simp; constructor
    apply IH₀; apply Hclosed.left
    apply IH₁; apply Hclosed.right
  | lit => simp
  | fix _ IH
  | lift _ IH
  | fix𝕔 _ IH
  | code _ IH
  | reflect _ IH
  | run _ IH =>
    simp; apply IH; apply Hclosed

lemma closed.under_shiftr_dec :
  ∀ x y e, closed_at e (x + y + 1) → y ∉ fv e → closed_at (shiftr_at y e) (x + y) :=
  by
  intros x y e Hclosed HFv
  cases x
  case zero =>
    simp at *
    apply closed.under_shiftr
    apply closed.fv_not_in_dec
    apply Hclosed; apply HFv
  case succ x =>
    induction e with
    | bvar j => simp
    | fvar z =>
      by_cases Hyz : y < z
      . simp; rw [if_pos Hyz]; simp at *; omega
      . simp; rw [if_neg Hyz]; simp at *; omega
    | app₁ _ _ IH₀ IH₁
    | app₂ _ _ IH₀ IH₁
    | lets _ _ IH₀ IH₁
    | lets𝕔 _ _ IH₀ IH₁ =>
      simp at HFv
      simp; constructor
      apply IH₀; apply HFv.left; apply Hclosed.left
      apply IH₁; apply HFv.right; apply Hclosed.right
    | lit => simp
    | fix _ IH
    | lift _ IH
    | fix𝕔 _ IH
    | code _ IH
    | reflect _ IH
    | run _ IH =>
      apply IH; apply HFv; apply Hclosed

lemma closed.under_erase : ∀ e x, closed_at e x ↔ closed_at ‖e‖ x :=
  by
  intros e x
  induction e with
  | fvar| lit| bvar => simp
  | app₁ _ _ IH₀ IH₁
  | app₂ _ _ IH₀ IH₁
  | lets _ _ IH₀ IH₁
  | lets𝕔 _ _ IH₀ IH₁ =>
    apply and_congr
    apply IH₀; apply IH₁
  | code _ IH
  | reflect _ IH
  | lift _ IH
  | run _ IH
  | fix _ IH
  | fix𝕔 _ IH =>
    apply IH

lemma closed.under_multi_subst : ∀ γ e, multi_wf γ → closed_at e γ.length → closed (multi_subst γ e) :=
  by
  intros γ e Hγ He
  induction γ generalizing e
  case nil => apply He
  case cons IH =>
    apply IH; apply Hγ.right
    apply closed.under_subst_dec; apply closed.inc
    apply Hγ.left.right; omega; apply He

lemma closed_impl_fv_not_in :
  ∀ x y e,
    closed_at e x →
    y ≥ x →
    y ∉ fv e :=
  by
  intros x y e Hclosed HGe HIn
  induction e with
  | bvar => nomatch HIn
  | fvar z =>
    simp at *
    omega
  | lit => nomatch HIn
  | fix _ IH
  | lift _ IH
  | fix𝕔 _ IH
  | code _ IH
  | reflect _ IH
  | run _ IH =>
    apply IH; apply Hclosed; apply HIn
  | app₁ _ _ IH₀ IH₁
  | app₂ _ _ IH₀ IH₁
  | lets _ _ IH₀ IH₁
  | lets𝕔 _ _ IH₀ IH₁ =>
    cases HIn
    case inl H₀ =>
      apply IH₀; apply Hclosed.left; apply H₀
    case inr H₁ =>
      apply IH₁; apply Hclosed.right; apply H₁

lemma closed_iff_fv_empty : ∀ e, closed e ↔ fv e = (∅ : Set ℕ) :=
  by
  intro e
  induction e with
  | bvar => simp
  | fvar => simp
  | lit => simp
  | fix _ IH
  | lift _ IH
  | fix𝕔 _ IH
  | code _ IH
  | reflect _ IH
  | run _ IH =>
    apply IH
  | app₁ _ _ IH₀ IH₁
  | app₂ _ _ IH₀ IH₁
  | lets _ _ IH₀ IH₁
  | lets𝕔 _ _ IH₀ IH₁ =>
    constructor
    . intro HFv; simp at HFv
      simp; constructor
      apply IH₀.mp; apply HFv.left
      apply IH₁.mp; apply HFv.right
    . intro Hclosed; simp at Hclosed
      simp; constructor
      apply IH₀.mpr; apply Hclosed.left
      apply IH₁.mpr; apply Hclosed.right

lemma lc.inc:
  ∀ e i j,
    lc_at e i → i ≤ j →
    lc_at e j :=
  by
  intros e i j Hclosed HLe
  induction e generalizing i j with
  | bvar => simp at *; omega
  | fvar => simp
  | fix _ IH
  | lift _ IH
  | fix𝕔 _ IH
  | code _ IH
  | reflect _ IH
  | run _ IH =>
    apply IH; apply Hclosed; omega
  | app₁ _ _ IH₀ IH₁
  | app₂ _ _ IH₀ IH₁
  | lets _ _ IH₀ IH₁
  | lets𝕔 _ _ IH₀ IH₁ =>
    apply And.intro
    . apply IH₀; apply Hclosed.left; omega
    . apply IH₁; apply Hclosed.right; omega
  | lit => simp

lemma lc.under_opening : ∀ i x e, lc_at ({i ↦ x} e) i ↔ lc_at e (i + 1) :=
  by
  intros i x e
  induction e generalizing i with
  | bvar j =>
    by_cases HEq : j = i
    . simp [if_pos HEq]; omega
    . simp [if_neg HEq]; omega
  | fvar => simp
  | lit => simp
  | fix _ IH
  | lift _ IH
  | fix𝕔 _ IH
  | code _ IH
  | reflect _ IH
  | run _ IH =>
    apply IH
  | app₁ _ _ IH₀ IH₁
  | app₂ _ _ IH₀ IH₁
  | lets _ _ IH₀ IH₁
  | lets𝕔 _ _ IH₀ IH₁ =>
    constructor
    . intro Hlc
      constructor
      apply (IH₀ _).mp; apply Hlc.left
      apply (IH₁ _).mp; apply Hlc.right
    . intro Hlc
      constructor
      apply (IH₀ _).mpr; apply Hlc.left
      apply (IH₁ _).mpr; apply Hlc.right

lemma lc.under_closing : ∀ e x i j, j < i → lc_at e i → lc_at ({j ↤ x} e) i :=
  by
  intros e x i j Hlt
  induction e generalizing i j with
  | fvar y =>
    by_cases HEq : x = y
    . rw [HEq]; simp; omega
    . simp; rw [if_neg HEq]; simp
  | bvar => simp
  | fix _ IH
  | lift _ IH
  | fix𝕔 _ IH
  | code _ IH
  | reflect _ IH
  | run _ IH =>
    apply IH; omega
  | app₁ _ _ IH₀ IH₁
  | app₂ _ _ IH₀ IH₁
  | lets _ _ IH₀ IH₁
  | lets𝕔 _ _ IH₀ IH₁ =>
    intro Hlc; constructor
    apply IH₀; omega; apply Hlc.left
    apply IH₁; omega; apply Hlc.right
  | lit => simp

lemma lc.under_subst : ∀ x e v i, lc_at v i → lc_at e i → lc_at (subst x v e) i :=
  by
  intros x e v i Hv He
  induction e generalizing i with
  | bvar => apply He
  | fvar y =>
    by_cases HEq : x = y
    . rw [HEq]; simp; apply Hv
    . simp; rw [if_neg HEq]; simp
  | fix _ IH
  | lift _ IH
  | fix𝕔 _ IH =>
    apply IH; apply lc.inc
    apply Hv; omega; apply He
  | app₁ _ _ IH₀ IH₁
  | app₂ _ _ IH₀ IH₁ =>
    constructor
    apply IH₀; apply Hv; apply He.left
    apply IH₁; apply Hv; apply He.right
  | lets _ _ IHb IH
  | lets𝕔 _ _ IHb IH =>
    constructor
    apply IHb; apply Hv; apply He.left
    apply IH; apply lc.inc
    apply Hv; omega; apply He.right
  | code _ IH
  | reflect _ IH
  | run _ IH =>
    simp; apply IH; apply Hv; apply He
  | lit => simp

lemma lc.under_multi_subst : ∀ i γ e, multi_wf γ → lc_at e i → lc_at (multi_subst γ e) i :=
  by
  intros i γ e Hγ He
  induction γ generalizing e
  case nil => apply He
  case cons IH =>
    apply IH; apply Hγ.right
    apply lc.under_subst; apply lc.inc
    apply Hγ.left.left; omega; apply He

lemma lc.under_erase : ∀ e i, lc_at e i ↔ lc_at ‖e‖ i :=
  by
  intros e i
  induction e generalizing i with
  | fvar| lit| bvar => simp
  | app₁ _ _ IH₀ IH₁
  | app₂ _ _ IH₀ IH₁
  | lets _ _ IH₀ IH₁
  | lets𝕔 _ _ IH₀ IH₁ =>
    apply and_congr
    apply IH₀; apply IH₁
  | code _ IH
  | reflect _ IH
  | lift _ IH
  | run _ IH
  | fix _ IH
  | fix𝕔 _ IH =>
    apply IH
