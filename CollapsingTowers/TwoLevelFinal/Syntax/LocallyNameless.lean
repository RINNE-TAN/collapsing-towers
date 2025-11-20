import CollapsingTowers.TwoLevelFinal.Syntax.Transform
import CollapsingTowers.TwoLevelFinal.Syntax.Fv

-- closedness condition for free variables
@[simp]
def closed_at (e : Expr) (x : ℕ) : Prop :=
  match e with
  | .bvar _ => true
  | .fvar y => y < x
  | .lam e => closed_at e x
  | .lift e => closed_at e x
  | .app₁ f arg => closed_at f x ∧ closed_at arg x
  | .app₂ f arg => closed_at f x ∧ closed_at arg x
  | .binary₁ _ l r => closed_at l x ∧ closed_at r x
  | .binary₂ _ l r => closed_at l x ∧ closed_at r x
  | .lit _ => true
  | .run e => closed_at e x
  | .code e => closed_at e x
  | .reflect e => closed_at e x
  | .lam𝕔 e => closed_at e x
  | .lets b e => closed_at b x ∧ closed_at e x
  | .lets𝕔 b e => closed_at b x ∧ closed_at e x
  | .unit => true
  | .loc _ => true
  | .alloc₁ e => closed_at e x
  | .alloc₂ e => closed_at e x
  | .load₁ e => closed_at e x
  | .load₂ e => closed_at e x
  | .store₁ l r => closed_at l x ∧ closed_at r x
  | .store₂ l r => closed_at l x ∧ closed_at r x
  | .fix₁ e => closed_at e x
  | .fix₂ e => closed_at e x
  | .ifz₁ c l r => closed_at c x ∧ closed_at l x ∧ closed_at r x
  | .ifz₂ c l r => closed_at c x ∧ closed_at l x ∧ closed_at r x

@[simp]
def closed e := closed_at e 0

-- closedness condition for bound variables
@[simp]
def lc_at (e : Expr) (i : ℕ) : Prop :=
  match e with
  | .bvar j => j < i
  | .fvar _ => true
  | .lam e => lc_at e (i + 1)
  | .lift e => lc_at e i
  | .app₁ f arg => lc_at f i ∧ lc_at arg i
  | .app₂ f arg => lc_at f i ∧ lc_at arg i
  | .binary₁ _ l r => lc_at l i ∧ lc_at r i
  | .binary₂ _ l r => lc_at l i ∧ lc_at r i
  | .lit _ => true
  | .run e => lc_at e i
  | .code e => lc_at e i
  | .reflect e => lc_at e i
  | .lam𝕔 e => lc_at e (i + 1)
  | .lets b e => lc_at b i ∧ lc_at e (i + 1)
  | .lets𝕔 b e => lc_at b i ∧ lc_at e (i + 1)
  | .unit => true
  | .loc _ => true
  | .alloc₁ e => lc_at e i
  | .alloc₂ e => lc_at e i
  | .load₁ e => lc_at e i
  | .load₂ e => lc_at e i
  | .store₁ l r => lc_at l i ∧ lc_at r i
  | .store₂ l r => lc_at l i ∧ lc_at r i
  | .fix₁ e => lc_at e i
  | .fix₂ e => lc_at e i
  | .ifz₁ c l r => lc_at c i ∧ lc_at l i ∧ lc_at r i
  | .ifz₂ c l r => lc_at c i ∧ lc_at l i ∧ lc_at r i

@[simp]
def lc e := lc_at e 0

@[simp]
def wf_at (e : Expr) (x : ℕ) : Prop := lc e ∧ closed_at e x

@[simp]
def wf (e : Expr) : Prop := wf_at e 0

@[simp]
def mwf : Subst → Prop
  | [] => true
  | v :: γ => wf v ∧ mwf γ

lemma closed.inc : ∀ x y e, closed_at e x → x ≤ y → closed_at e y :=
  by
  intros x y e Hclosed Hxy
  induction e with
  | bvar| lit| unit| loc => simp
  | fvar => simp at *; omega
  | app₁ _ _ IH₀ IH₁
  | app₂ _ _ IH₀ IH₁
  | binary₁ _ _ _ IH₀ IH₁
  | binary₂ _ _ _ IH₀ IH₁
  | store₁ _ _ IH₀ IH₁
  | store₂ _ _ IH₀ IH₁
  | lets _ _ IH₀ IH₁
  | lets𝕔 _ _ IH₀ IH₁ =>
    simp; constructor
    apply IH₀; apply Hclosed.left
    apply IH₁; apply Hclosed.right
  | lam _ IH
  | lift _ IH
  | lam𝕔 _ IH
  | code _ IH
  | reflect _ IH
  | run _ IH
  | alloc₁ _ IH
  | alloc₂ _ IH
  | load₁ _ IH
  | load₂ _ IH
  | fix₁ _ IH
  | fix₂ _ IH =>
    apply IH; apply Hclosed
  | ifz₁ _ _ _ IH₀ IH₁ IH₂
  | ifz₂ _ _ _ IH₀ IH₁ IH₂ =>
    simp; constructor
    apply IH₀; apply Hclosed.left; constructor
    apply IH₁; apply Hclosed.right.left
    apply IH₂; apply Hclosed.right.right

lemma closed.dec.not_in_fv : ∀ e x, closed_at e (x + 1) → x ∉ fv e → closed_at e x :=
  by
  intros e x Hclosed HFv
  induction e with
  | bvar| lit| unit| loc => simp
  | fvar y => simp at *; omega
  | lift _ IH
  | code _ IH
  | reflect _ IH
  | run _ IH
  | alloc₁ _ IH
  | alloc₂ _ IH
  | load₁ _ IH
  | load₂ _ IH
  | lam _ IH
  | lam𝕔 _ IH
  | fix₁ _ IH
  | fix₂ _ IH =>
    apply IH; apply Hclosed; apply HFv
  | app₁ _ _ IH₀ IH₁
  | app₂ _ _ IH₀ IH₁
  | binary₁ _ _ _ IH₀ IH₁
  | binary₂ _ _ _ IH₀ IH₁
  | store₁ _ _ IH₀ IH₁
  | store₂ _ _ IH₀ IH₁
  | lets _ _ IH₀ IH₁
  | lets𝕔 _ _ IH₀ IH₁ =>
    simp at HFv; constructor
    apply IH₀; apply Hclosed.left; apply HFv.left
    apply IH₁; apply Hclosed.right; apply HFv.right
  | ifz₁ _ _ _ IH₀ IH₁ IH₂
  | ifz₂ _ _ _ IH₀ IH₁ IH₂ =>
    simp at HFv; constructor
    apply IH₀; apply Hclosed.left; apply HFv.left.left; constructor
    apply IH₁; apply Hclosed.right.left; apply HFv.left.right
    apply IH₂; apply Hclosed.right.right; apply HFv.right

lemma closed.dec.under_subst : ∀ x e v, closed_at v x → closed_at e (x + 1) → closed_at (subst x v e) x :=
  by
  intros x e v Hv He
  induction e with
  | bvar => apply He
  | fvar z =>
    by_cases HEq : x = z
    . simp [if_pos HEq]; apply Hv
    . simp [if_neg HEq]; simp at He; omega
  | lit| unit| loc => simp
  | lam _ IH
  | lift _ IH
  | lam𝕔 _ IH =>
    apply IH; apply He
  | app₁ _ _ IH₀ IH₁
  | app₂ _ _ IH₀ IH₁
  | binary₁ _ _ _ IH₀ IH₁
  | binary₂ _ _ _ IH₀ IH₁
  | store₁ _ _ IH₀ IH₁
  | store₂ _ _ IH₀ IH₁
  | lets _ _ IH₀ IH₁
  | lets𝕔 _ _ IH₀ IH₁ =>
    constructor
    apply IH₀; apply He.left
    apply IH₁; apply He.right
  | code _ IH
  | reflect _ IH
  | run _ IH
  | alloc₁ _ IH
  | alloc₂ _ IH
  | load₁ _ IH
  | load₂ _ IH
  | fix₁ _ IH
  | fix₂ _ IH =>
    simp; apply IH; apply He
  | ifz₁ _ _ _ IH₀ IH₁ IH₂
  | ifz₂ _ _ _ IH₀ IH₁ IH₂ =>
    constructor
    apply IH₀; apply He.left; constructor
    apply IH₁; apply He.right.left
    apply IH₂; apply He.right.right

lemma closed.under_closing : ∀ e x i, closed_at e (x + 1) ↔ closed_at ({i ↤ x} e) x :=
  by
  intros e x i
  induction e generalizing i with
  | bvar| lit| unit| loc => simp
  | fvar y =>
    by_cases HEq : x = y
    . simp [HEq]
    . simp [if_neg HEq]; omega
  | lam _ IH
  | lift _ IH
  | lam𝕔 _ IH
  | code _ IH
  | reflect _ IH
  | run _ IH
  | alloc₁ _ IH
  | alloc₂ _ IH
  | load₁ _ IH
  | load₂ _ IH
  | fix₁ _ IH
  | fix₂ _ IH =>
    apply IH
  | app₁ _ _ IH₀ IH₁
  | app₂ _ _ IH₀ IH₁
  | binary₁ _ _ _ IH₀ IH₁
  | binary₂ _ _ _ IH₀ IH₁
  | store₁ _ _ IH₀ IH₁
  | store₂ _ _ IH₀ IH₁
  | lets _ _ IH₀ IH₁
  | lets𝕔 _ _ IH₀ IH₁ =>
    constructor
    . intro Hclosed; constructor
      apply (IH₀ _).mp; apply Hclosed.left
      apply (IH₁ _).mp; apply Hclosed.right
    . intro Hclosed; constructor
      apply (IH₀ _).mpr; apply Hclosed.left
      apply (IH₁ _).mpr; apply Hclosed.right
  | ifz₁ _ _ _ IH₀ IH₁ IH₂
  | ifz₂ _ _ _ IH₀ IH₁ IH₂ =>
    constructor
    . intro Hclosed; constructor
      apply (IH₀ _).mp; apply Hclosed.left; constructor
      apply (IH₁ _).mp; apply Hclosed.right.left
      apply (IH₂ _).mp; apply Hclosed.right.right
    . intro Hclosed; constructor
      apply (IH₀ _).mpr; apply Hclosed.left; constructor
      apply (IH₁ _).mpr; apply Hclosed.right.left
      apply (IH₂ _).mpr; apply Hclosed.right.right

lemma closed.under_opening : ∀ e x i, closed_at e x → closed_at ({i ↦ x} e) (x + 1) :=
  by
  intros e x i
  induction e generalizing i with
  | fvar y => simp; omega
  | bvar j =>
    by_cases HEq : j = i
    . rw [HEq]; simp
    . simp; rw [if_neg HEq]; simp
  | lit| unit| loc => simp
  | lam _ IH
  | lift _ IH
  | lam𝕔 _ IH
  | code _ IH
  | reflect _ IH
  | run _ IH
  | alloc₁ _ IH
  | alloc₂ _ IH
  | load₁ _ IH
  | load₂ _ IH
  | fix₁ _ IH
  | fix₂ _ IH =>
    apply IH
  | app₁ _ _ IH₀ IH₁
  | app₂ _ _ IH₀ IH₁
  | binary₁ _ _ _ IH₀ IH₁
  | binary₂ _ _ _ IH₀ IH₁
  | store₁ _ _ IH₀ IH₁
  | store₂ _ _ IH₀ IH₁
  | lets _ _ IH₀ IH₁
  | lets𝕔 _ _ IH₀ IH₁ =>
    intro Hclosed; constructor
    apply IH₀; apply Hclosed.left
    apply IH₁; apply Hclosed.right
  | ifz₁ _ _ _ IH₀ IH₁ IH₂
  | ifz₂ _ _ _ IH₀ IH₁ IH₂ =>
    intro Hclosed; constructor
    apply IH₀; apply Hclosed.left; constructor
    apply IH₁; apply Hclosed.right.left
    apply IH₂; apply Hclosed.right.right

lemma closed.under_shiftl : ∀ x y e n, closed_at e x → closed_at (shiftl y n e) (x + n) :=
  by
  intros x y e n Hclosed
  induction e with
  | bvar j => simp
  | fvar z =>
    by_cases HLe : y ≤ z
    . simp [if_pos HLe]; apply Hclosed
    . simp [if_neg HLe]; simp at Hclosed; omega
  | app₁ _ _ IH₀ IH₁
  | app₂ _ _ IH₀ IH₁
  | binary₁ _ _ _ IH₀ IH₁
  | binary₂ _ _ _ IH₀ IH₁
  | store₁ _ _ IH₀ IH₁
  | store₂ _ _ IH₀ IH₁
  | lets _ _ IH₀ IH₁
  | lets𝕔 _ _ IH₀ IH₁ =>
    constructor
    apply IH₀; apply Hclosed.left
    apply IH₁; apply Hclosed.right
  | lit| unit| loc => simp
  | lam _ IH
  | lift _ IH
  | lam𝕔 _ IH
  | code _ IH
  | reflect _ IH
  | run _ IH
  | alloc₁ _ IH
  | alloc₂ _ IH
  | load₁ _ IH
  | load₂ _ IH
  | fix₁ _ IH
  | fix₂ _ IH =>
    apply IH; apply Hclosed
  | ifz₁ _ _ _ IH₀ IH₁ IH₂
  | ifz₂ _ _ _ IH₀ IH₁ IH₂ =>
    constructor
    apply IH₀; apply Hclosed.left; constructor
    apply IH₁; apply Hclosed.right.left
    apply IH₂; apply Hclosed.right.right

lemma closed.under_subst : ∀ x e v y, closed_at v y → closed_at e y → closed_at (subst x v e) y :=
  by
  intros x e v y Hv He
  induction e generalizing y with
  | bvar => apply He
  | fvar z =>
    by_cases HEq : x = z
    . simp [if_pos HEq]; apply Hv
    . simp [if_neg HEq]; apply He
  | lit| unit| loc => simp
  | lam _ IH
  | lift _ IH
  | lam𝕔 _ IH =>
    apply IH; apply Hv; apply He
  | app₁ _ _ IH₀ IH₁
  | app₂ _ _ IH₀ IH₁
  | binary₁ _ _ _ IH₀ IH₁
  | binary₂ _ _ _ IH₀ IH₁
  | store₁ _ _ IH₀ IH₁
  | store₂ _ _ IH₀ IH₁
  | lets _ _ IH₀ IH₁
  | lets𝕔 _ _ IH₀ IH₁ =>
    constructor
    apply IH₀; apply Hv; apply He.left
    apply IH₁; apply Hv; apply He.right
  | code _ IH
  | reflect _ IH
  | run _ IH
  | alloc₁ _ IH
  | alloc₂ _ IH
  | load₁ _ IH
  | load₂ _ IH
  | fix₁ _ IH
  | fix₂ _ IH =>
    simp; apply IH; apply Hv; apply He
  | ifz₁ _ _ _ IH₀ IH₁ IH₂
  | ifz₂ _ _ _ IH₀ IH₁ IH₂ =>
    constructor
    apply IH₀; apply Hv; apply He.left; constructor
    apply IH₁; apply Hv; apply He.right.left
    apply IH₂; apply Hv; apply He.right.right

lemma closed.under_shiftr : ∀ x e, closed_at e x → closed_at (shiftr x e) x :=
  by
  intros x e Hclosed
  induction e with
  | bvar j => simp
  | fvar z =>
    by_cases Hxz : x < z
    . simp [if_pos Hxz]; simp at Hclosed; omega
    . simp [if_neg Hxz]; simp at Hclosed; omega
  | app₁ _ _ IH₀ IH₁
  | app₂ _ _ IH₀ IH₁
  | binary₁ _ _ _ IH₀ IH₁
  | binary₂ _ _ _ IH₀ IH₁
  | store₁ _ _ IH₀ IH₁
  | store₂ _ _ IH₀ IH₁
  | lets _ _ IH₀ IH₁
  | lets𝕔 _ _ IH₀ IH₁ =>
    simp; constructor
    apply IH₀; apply Hclosed.left
    apply IH₁; apply Hclosed.right
  | lit| unit| loc => simp
  | lam _ IH
  | lift _ IH
  | lam𝕔 _ IH
  | code _ IH
  | reflect _ IH
  | run _ IH
  | alloc₁ _ IH
  | alloc₂ _ IH
  | load₁ _ IH
  | load₂ _ IH
  | fix₁ _ IH
  | fix₂ _ IH =>
    apply IH; apply Hclosed
  | ifz₁ _ _ _ IH₀ IH₁ IH₂
  | ifz₂ _ _ _ IH₀ IH₁ IH₂ =>
    constructor
    apply IH₀; apply Hclosed.left; constructor
    apply IH₁; apply Hclosed.right.left
    apply IH₂; apply Hclosed.right.right

lemma closed.dec.under_shiftr :
  ∀ x y e, closed_at e (x + y + 1) → y ∉ fv e → closed_at (shiftr y e) (x + y) :=
  by
  intros x y e Hclosed HFv
  cases x
  case zero =>
    simp at *
    apply closed.under_shiftr
    apply closed.dec.not_in_fv
    apply Hclosed; apply HFv
  case succ x =>
    induction e with
    | bvar| lit| unit| loc => simp
    | fvar z =>
      by_cases HEq : y < z
      . simp [if_pos HEq]; simp at Hclosed; omega
      . simp [if_neg HEq]; simp at Hclosed; omega
    | lam _ IH
    | lift _ IH
    | lam𝕔 _ IH
    | code _ IH
    | reflect _ IH
    | run _ IH
    | alloc₁ _ IH
    | alloc₂ _ IH
    | load₁ _ IH
    | load₂ _ IH
    | fix₁ _ IH
    | fix₂ _ IH =>
      apply IH; apply HFv; apply Hclosed
    | app₁ _ _ IH₀ IH₁
    | app₂ _ _ IH₀ IH₁
    | binary₁ _ _ _ IH₀ IH₁
    | binary₂ _ _ _ IH₀ IH₁
    | store₁ _ _ IH₀ IH₁
    | store₂ _ _ IH₀ IH₁
    | lets _ _ IH₀ IH₁
    | lets𝕔 _ _ IH₀ IH₁ =>
      simp at HFv; constructor
      apply IH₀; apply HFv.left; apply Hclosed.left
      apply IH₁; apply HFv.right; apply Hclosed.right
    | ifz₁ _ _ _ IH₀ IH₁ IH₂
    | ifz₂ _ _ _ IH₀ IH₁ IH₂ =>
      simp at HFv; constructor
      apply IH₀; apply HFv.left.left; apply Hclosed.left; constructor
      apply IH₁; apply HFv.left.right; apply Hclosed.right.left
      apply IH₂; apply HFv.right; apply Hclosed.right.right

lemma closed.under_erase : ∀ e x, closed_at e x ↔ closed_at ‖e‖ x :=
  by
  intros e x
  induction e with
  | fvar| lit| bvar| unit| loc => simp
  | code _ IH
  | reflect _ IH
  | lift _ IH
  | run _ IH
  | alloc₁ _ IH
  | alloc₂ _ IH
  | load₁ _ IH
  | load₂ _ IH
  | lam _ IH
  | lam𝕔 _ IH
  | fix₁ _ IH
  | fix₂ _ IH =>
    simp [IH]
  | app₁ _ _ IH₀ IH₁
  | app₂ _ _ IH₀ IH₁
  | binary₁ _ _ _ IH₀ IH₁
  | binary₂ _ _ _ IH₀ IH₁
  | store₁ _ _ IH₀ IH₁
  | store₂ _ _ IH₀ IH₁
  | lets _ _ IH₀ IH₁
  | lets𝕔 _ _ IH₀ IH₁ =>
    simp [IH₀, IH₁]
  | ifz₁ _ _ _ IH₀ IH₁ IH₂
  | ifz₂ _ _ _ IH₀ IH₁ IH₂ =>
    simp [IH₀, IH₁, IH₂]

lemma closed.under_codify : ∀ e x i, closed_at e x ↔ closed_at (codify i e) x :=
  by
  intros e x i
  induction e generalizing i with
  | fvar| lit| unit| loc => simp
  | bvar j =>
    by_cases HEq : j = i
    . simp [if_pos HEq]
    . simp [if_neg HEq]
  | code _ IH
  | reflect _ IH
  | lift _ IH
  | run _ IH
  | alloc₁ _ IH
  | alloc₂ _ IH
  | load₁ _ IH
  | load₂ _ IH
  | fix₁ _ IH
  | fix₂ _ IH =>
    simp [IH i]
  | lam _ IH
  | lam𝕔 _ IH =>
    simp [IH (i + 1)]
  | app₁ _ _ IH₀ IH₁
  | app₂ _ _ IH₀ IH₁
  | binary₁ _ _ _ IH₀ IH₁
  | binary₂ _ _ _ IH₀ IH₁
  | store₁ _ _ IH₀ IH₁
  | store₂ _ _ IH₀ IH₁ =>
    simp [IH₀ i, IH₁ i]
  | lets _ _ IH₀ IH₁
  | lets𝕔 _ _ IH₀ IH₁ =>
    simp [IH₀ i, IH₁ (i + 1)]
  | ifz₁ _ _ _ IH₀ IH₁ IH₂
  | ifz₂ _ _ _ IH₀ IH₁ IH₂ =>
    simp [IH₀ i, IH₁ i, IH₂ i]

lemma closed.under_msubst : ∀ γ e, mwf γ → closed_at e γ.length → closed (msubst γ e) :=
  by
  intros γ e Hγ He
  induction γ generalizing e
  case nil => apply He
  case cons IH =>
    apply IH; apply Hγ.right
    apply closed.dec.under_subst; apply closed.inc
    apply Hγ.left.right; omega; apply He

lemma closed_impl_not_in_fv :
  ∀ x y e,
    closed_at e x →
    y ≥ x →
    y ∉ fv e :=
  by
  intros x y e Hclosed HGe HIn
  induction e with
  | bvar| lit| unit| loc => nomatch HIn
  | fvar => simp at *; omega
  | lam _ IH
  | lift _ IH
  | lam𝕔 _ IH
  | code _ IH
  | reflect _ IH
  | run _ IH
  | alloc₁ _ IH
  | alloc₂ _ IH
  | load₁ _ IH
  | load₂ _ IH
  | fix₁ _ IH
  | fix₂ _ IH =>
    apply IH; apply Hclosed; apply HIn
  | app₁ _ _ IH₀ IH₁
  | app₂ _ _ IH₀ IH₁
  | binary₁ _ _ _ IH₀ IH₁
  | binary₂ _ _ _ IH₀ IH₁
  | store₁ _ _ IH₀ IH₁
  | store₂ _ _ IH₀ IH₁
  | lets _ _ IH₀ IH₁
  | lets𝕔 _ _ IH₀ IH₁ =>
    cases HIn
    case inl H₀ =>
      apply IH₀; apply Hclosed.left; apply H₀
    case inr H₁ =>
      apply IH₁; apply Hclosed.right; apply H₁
  | ifz₁ _ _ _ IH₀ IH₁ IH₂
  | ifz₂ _ _ _ IH₀ IH₁ IH₂ =>
    cases HIn
    case inl HIn =>
      cases HIn
      case inl H₀ =>
        apply IH₀; apply Hclosed.left; apply H₀
      case inr H₁ =>
        apply IH₁; apply Hclosed.right.left; apply H₁
    case inr H₂ =>
      apply IH₂; apply Hclosed.right.right; apply H₂

lemma closed_iff_fv_empty : ∀ e, closed e ↔ fv e = ∅ :=
  by
  intro e
  induction e with
  | bvar => simp
  | fvar => simp
  | lit| unit| loc => simp
  | lam _ IH
  | lift _ IH
  | lam𝕔 _ IH
  | code _ IH
  | reflect _ IH
  | run _ IH
  | alloc₁ _ IH
  | alloc₂ _ IH
  | load₁ _ IH
  | load₂ _ IH
  | fix₁ _ IH
  | fix₂ _ IH =>
    apply IH
  | app₁ _ _ IH₀ IH₁
  | app₂ _ _ IH₀ IH₁
  | binary₁ _ _ _ IH₀ IH₁
  | binary₂ _ _ _ IH₀ IH₁
  | store₁ _ _ IH₀ IH₁
  | store₂ _ _ IH₀ IH₁
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
  | ifz₁ _ _ _ IH₀ IH₁ IH₂
  | ifz₂ _ _ _ IH₀ IH₁ IH₂ =>
    constructor
    . intro HFv; simp at HFv
      simp; constructor; constructor
      apply IH₀.mp; apply HFv.left
      apply IH₁.mp; apply HFv.right.left
      apply IH₂.mp; apply HFv.right.right
    . intro Hclosed; simp at Hclosed
      simp; constructor
      apply IH₀.mpr; apply Hclosed.left.left; constructor
      apply IH₁.mpr; apply Hclosed.left.right
      apply IH₂.mpr; apply Hclosed.right

lemma lc.inc: ∀ e i j, lc_at e i → i ≤ j → lc_at e j :=
  by
  intros e i j Hclosed HLe
  induction e generalizing i j with
  | bvar => simp at *; omega
  | fvar| lit| unit| loc => simp
  | lam _ IH
  | lift _ IH
  | lam𝕔 _ IH
  | code _ IH
  | reflect _ IH
  | run _ IH
  | alloc₁ _ IH
  | alloc₂ _ IH
  | load₁ _ IH
  | load₂ _ IH
  | fix₁ _ IH
  | fix₂ _ IH =>
    apply IH; apply Hclosed; omega
  | app₁ _ _ IH₀ IH₁
  | app₂ _ _ IH₀ IH₁
  | binary₁ _ _ _ IH₀ IH₁
  | binary₂ _ _ _ IH₀ IH₁
  | store₁ _ _ IH₀ IH₁
  | store₂ _ _ IH₀ IH₁
  | lets _ _ IH₀ IH₁
  | lets𝕔 _ _ IH₀ IH₁ =>
    constructor
    apply IH₀; apply Hclosed.left; omega
    apply IH₁; apply Hclosed.right; omega
  | ifz₁ _ _ _ IH₀ IH₁ IH₂
  | ifz₂ _ _ _ IH₀ IH₁ IH₂ =>
    constructor
    apply IH₀; apply Hclosed.left; omega; constructor
    apply IH₁; apply Hclosed.right.left; omega
    apply IH₂; apply Hclosed.right.right; omega

lemma lc.under_opening : ∀ i x e, lc_at ({i ↦ x} e) i ↔ lc_at e (i + 1) :=
  by
  intros i x e
  induction e generalizing i with
  | bvar j =>
    by_cases HEq : j = i
    . simp [if_pos HEq]; omega
    . simp [if_neg HEq]; omega
  | fvar => simp
  | lit| unit| loc => simp
  | lam _ IH
  | lift _ IH
  | lam𝕔 _ IH
  | code _ IH
  | reflect _ IH
  | run _ IH
  | alloc₁ _ IH
  | alloc₂ _ IH
  | load₁ _ IH
  | load₂ _ IH
  | fix₁ _ IH
  | fix₂ _ IH =>
    apply IH
  | app₁ _ _ IH₀ IH₁
  | app₂ _ _ IH₀ IH₁
  | binary₁ _ _ _ IH₀ IH₁
  | binary₂ _ _ _ IH₀ IH₁
  | store₁ _ _ IH₀ IH₁
  | store₂ _ _ IH₀ IH₁
  | lets _ _ IH₀ IH₁
  | lets𝕔 _ _ IH₀ IH₁ =>
    constructor
    . intro Hlc; constructor
      apply (IH₀ _).mp; apply Hlc.left
      apply (IH₁ _).mp; apply Hlc.right
    . intro Hlc; constructor
      apply (IH₀ _).mpr; apply Hlc.left
      apply (IH₁ _).mpr; apply Hlc.right
  | ifz₁ _ _ _ IH₀ IH₁ IH₂
  | ifz₂ _ _ _ IH₀ IH₁ IH₂ =>
    constructor
    . intro Hlc; constructor
      apply (IH₀ _).mp; apply Hlc.left; constructor
      apply (IH₁ _).mp; apply Hlc.right.left
      apply (IH₂ _).mp; apply Hlc.right.right
    . intro Hlc; constructor
      apply (IH₀ _).mpr; apply Hlc.left; constructor
      apply (IH₁ _).mpr; apply Hlc.right.left
      apply (IH₂ _).mpr; apply Hlc.right.right

lemma lc.under_closing : ∀ e x i j, j < i → lc_at e i → lc_at ({j ↤ x} e) i :=
  by
  intros e x i j Hlt
  induction e generalizing i j with
  | bvar| lit| unit| loc => simp
  | fvar y =>
    by_cases HEq : x = y
    . rw [HEq]; simp; omega
    . simp; rw [if_neg HEq]; simp
  | lam _ IH
  | lift _ IH
  | lam𝕔 _ IH
  | code _ IH
  | reflect _ IH
  | run _ IH
  | alloc₁ _ IH
  | alloc₂ _ IH
  | load₁ _ IH
  | load₂ _ IH
  | fix₁ _ IH
  | fix₂ _ IH =>
    apply IH; omega
  | app₁ _ _ IH₀ IH₁
  | app₂ _ _ IH₀ IH₁
  | binary₁ _ _ _ IH₀ IH₁
  | binary₂ _ _ _ IH₀ IH₁
  | store₁ _ _ IH₀ IH₁
  | store₂ _ _ IH₀ IH₁
  | lets _ _ IH₀ IH₁
  | lets𝕔 _ _ IH₀ IH₁ =>
    intro Hlc; constructor
    apply IH₀; omega; apply Hlc.left
    apply IH₁; omega; apply Hlc.right
  | ifz₁ _ _ _ IH₀ IH₁ IH₂
  | ifz₂ _ _ _ IH₀ IH₁ IH₂ =>
    intro Hlc; constructor
    apply IH₀; omega; apply Hlc.left; constructor
    apply IH₁; omega; apply Hlc.right.left
    apply IH₂; omega; apply Hlc.right.right

lemma lc.under_subst : ∀ x e v i, lc_at v i → lc_at e i → lc_at (subst x v e) i :=
  by
  intros x e v i Hv He
  induction e generalizing i with
  | bvar => apply He
  | fvar y =>
    by_cases HEq : x = y
    . simp [if_pos HEq]; apply Hv
    . simp [if_neg HEq]
  | lit| unit| loc => simp
  | lam _ IH
  | lift _ IH
  | lam𝕔 _ IH =>
    apply IH; apply lc.inc
    apply Hv; omega; apply He
  | app₁ _ _ IH₀ IH₁
  | app₂ _ _ IH₀ IH₁
  | binary₁ _ _ _ IH₀ IH₁
  | binary₂ _ _ _ IH₀ IH₁
  | store₁ _ _ IH₀ IH₁
  | store₂ _ _ IH₀ IH₁ =>
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
  | run _ IH
  | alloc₁ _ IH
  | alloc₂ _ IH
  | load₁ _ IH
  | load₂ _ IH
  | fix₁ _ IH
  | fix₂ _ IH =>
    apply IH; apply Hv; apply He
  | ifz₁ _ _ _ IH₀ IH₁ IH₂
  | ifz₂ _ _ _ IH₀ IH₁ IH₂ =>
    constructor
    apply IH₀; apply Hv; apply He.left; constructor
    apply IH₁; apply Hv; apply He.right.left
    apply IH₂; apply Hv; apply He.right.right

lemma lc.under_msubst : ∀ i γ e, mwf γ → lc_at e i → lc_at (msubst γ e) i :=
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
  | fvar| lit| bvar| unit| loc => simp
  | code _ IH
  | reflect _ IH
  | lift _ IH
  | run _ IH
  | alloc₁ _ IH
  | alloc₂ _ IH
  | load₁ _ IH
  | load₂ _ IH
  | lam _ IH
  | lam𝕔 _ IH
  | fix₁ _ IH
  | fix₂ _ IH =>
    simp [IH]
  | app₁ _ _ IH₀ IH₁
  | app₂ _ _ IH₀ IH₁
  | binary₁ _ _ _ IH₀ IH₁
  | binary₂ _ _ _ IH₀ IH₁
  | store₁ _ _ IH₀ IH₁
  | store₂ _ _ IH₀ IH₁
  | lets _ _ IH₀ IH₁
  | lets𝕔 _ _ IH₀ IH₁ =>
    simp [IH₀, IH₁]
  | ifz₁ _ _ _ IH₀ IH₁ IH₂
  | ifz₂ _ _ _ IH₀ IH₁ IH₂ =>
    simp [IH₀, IH₁, IH₂]
