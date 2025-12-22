import CollapsingTowers.TwoLevelMut.Syntax.Transform

@[simp]
def grounded (e : Expr) : Prop :=
  match e with
  | .bvar _ => true
  | .fvar _ => true
  | .lam e => grounded e
  | .lift _ => false
  | .app₁ f arg => grounded f ∧ grounded arg
  | .app₂ _ _ => false
  | .lit _ => true
  | .run _ => false
  | .code _ => false
  | .reflect _ => false
  | .lam𝕔 _ => false
  | .lets b e => grounded b ∧ grounded e
  | .lets𝕔 _ _ => false
  | .unit => true
  | .loc _ => true
  | .alloc₁ e => grounded e
  | .alloc₂ _ => false
  | .load₁ e => grounded e
  | .load₂ _ => false
  | .store₁ l r => grounded l ∧ grounded r
  | .store₂ _ _ => false

@[simp]
def mgrounded : Subst → Prop
  | [] => true
  | v :: γ => grounded v ∧ mgrounded γ

lemma grounded.under_erase : ∀ e, grounded ‖e‖ :=
  by
  intros e
  induction e with
  | bvar| fvar| lit| unit| loc => simp
  | lam _ IH
  | lift _ IH
  | lam𝕔 _ IH
  | code _ IH
  | reflect _ IH
  | run _ IH
  | alloc₁ _ IH
  | alloc₂ _ IH
  | load₁ _ IH
  | load₂ _ IH =>
    simp [IH]
  | app₁ _ _ IH₀ IH₁
  | app₂ _ _ IH₀ IH₁
  | store₁ _ _ IH₀ IH₁
  | store₂ _ _ IH₀ IH₁
  | lets _ _ IH₀ IH₁
  | lets𝕔 _ _ IH₀ IH₁ =>
    simp [IH₀, IH₁]

lemma erasable.lift : ∀ e₀ e₁, ‖e₀‖ ≠ Expr.lift e₁ :=
  by
  intros e₀ e₁
  induction e₀ <;> simp
  all_goals next IH => apply IH

lemma erasable.run : ∀ e₀ e₁, ‖e₀‖ ≠ Expr.run e₁ :=
  by
  intros e₀ e₁
  induction e₀ <;> simp
  all_goals next IH => apply IH

lemma erasable.code : ∀ e₀ e₁, ‖e₀‖ ≠ Expr.code e₁ :=
  by
  intros e₀ e₁
  induction e₀ <;> simp
  all_goals next IH => apply IH

lemma erasable.reflect : ∀ e₀ e₁, ‖e₀‖ ≠ Expr.reflect e₁ :=
  by
  intros e₀ e₁
  induction e₀ <;> simp
  all_goals next IH => apply IH

lemma grounded_iff_erase_identity : ∀ e, grounded e ↔ ‖e‖ = e :=
  by
  intros e
  induction e with
  | bvar| fvar| app₂| lit| lam𝕔| lets𝕔| unit| loc => simp
  | lam _ IH
  | alloc₁ _ IH
  | alloc₂ _ IH
  | load₁ _ IH
  | load₂ _ IH =>
    simp [IH]
  | app₁ _ _ IH₀ IH₁
  | lets _ _ IH₀ IH₁
  | store₁ _ _ IH₀ IH₁
  | store₂ _ _ IH₀ IH₁ =>
    simp [IH₀, IH₁]
  | lift => simp; apply erasable.lift
  | run => simp; apply erasable.run
  | code => simp; apply erasable.code
  | reflect => simp; apply erasable.reflect

lemma grounded.under_opening : ∀ e i x, grounded e ↔ grounded ({i ↦ x} e) :=
  by
  intros e i x
  induction e generalizing i with
  | fvar| app₂| lit| lam𝕔| lets𝕔| lift| run| code| reflect| unit| loc| alloc₂| load₂| store₂ => simp
  | bvar j =>
    by_cases HEq : j = i
    . simp [if_pos HEq]
    . simp [if_neg HEq]
  | lam _ IH
  | alloc₁ _ IH
  | load₁ _ IH =>
    apply IH
  | app₁ _ _ IH₀ IH₁
  | store₁ _ _ IH₀ IH₁
  | lets _ _ IH₀ IH₁ =>
    simp; rw [IH₀, IH₁]

lemma grounded.under_subst : ∀ e v x, grounded v → grounded e → grounded (subst x v e) :=
  by
  intros e v x
  induction e with
  | bvar| app₂| lit| lam𝕔| lets𝕔| lift| run| code| reflect| unit| loc| alloc₂| load₂| store₂ => simp
  | fvar y =>
    intros Hv
    by_cases HEq : x = y
    . simp [if_pos HEq, Hv]
    . simp [if_neg HEq]
  | lam _ IH
  | alloc₁ _ IH
  | load₁ _ IH =>
    apply IH
  | app₁ _ _ IH₀ IH₁
  | store₁ _ _ IH₀ IH₁
  | lets _ _ IH₀ IH₁ =>
    simp; intros Hv H₀ H₁; constructor
    apply IH₀; apply Hv; apply H₀
    apply IH₁; apply Hv; apply H₁

lemma grounded.under_msubst : ∀ γ e, mgrounded γ → grounded e → grounded (msubst γ e) :=
  by
  intros γ e HmG HG
  induction γ generalizing e
  case nil => apply HG
  case cons IH =>
    apply IH; apply HmG.right
    apply grounded.under_subst; apply HmG.left
    apply HG

lemma grounded.under_opening_value : ∀ e v i, grounded v → grounded e → grounded (opening i v e) :=
  by
  intros e v i
  induction e generalizing i with
  | fvar| app₂| lit| lam𝕔| lets𝕔| lift| run| code| reflect| unit| loc| alloc₂| load₂| store₂ => simp
  | bvar j =>
    simp; intros Hv
    by_cases HEq : j = i
    . simp [if_pos HEq, Hv]
    . simp [if_neg HEq]
  | lam _ IH
  | alloc₁ _ IH
  | load₁ _ IH =>
    apply IH
  | app₁ _ _ IH₀ IH₁
  | store₁ _ _ IH₀ IH₁
  | lets _ _ IH₀ IH₁ =>
    simp; intros Hv H₀ H₁; constructor
    apply IH₀; apply Hv; apply H₀
    apply IH₁; apply Hv; apply H₁

@[simp]
def store_free (e : Expr) : Prop :=
  match e with
  | .bvar _ => true
  | .fvar _ => true
  | .lam e => store_free e
  | .lift e => store_free e
  | .app₁ f arg => store_free f ∧ store_free arg
  | .app₂ f arg => store_free f ∧ store_free arg
  | .lit _ => true
  | .run e => store_free e
  | .code e => store_free e
  | .reflect e => store_free e
  | .lam𝕔 e => store_free e
  | .lets b e => store_free b ∧ store_free e
  | .lets𝕔 b e => store_free b ∧ store_free e
  | .unit => true
  | .loc _ => true
  | .alloc₁ _ => false
  | .alloc₂ _ => false
  | .load₁ _ => false
  | .load₂ _ => false
  | .store₁ _ _ => false
  | .store₂ _ _ => false

lemma store_free.under_opening : ∀ e i x, store_free e ↔ store_free ({i ↦ x} e) :=
  by
  intros e i x
  induction e generalizing i with
  | fvar| lit| unit| loc| alloc₁| alloc₂| load₁| load₂| store₁| store₂ => simp
  | bvar j =>
    by_cases HEq : j = i
    . simp [if_pos HEq]
    . simp [if_neg HEq]
  | lam _ IH
  | lift _ IH
  | lam𝕔 _ IH
  | code _ IH
  | reflect _ IH
  | run _ IH =>
    apply IH
  | app₁ _ _ IH₀ IH₁
  | app₂ _ _ IH₀ IH₁
  | lets _ _ IH₀ IH₁
  | lets𝕔 _ _ IH₀ IH₁ =>
    simp; rw [IH₀, IH₁]

lemma store_free.under_closing : ∀ e i x, store_free e ↔ store_free ({i ↤ x} e) :=
  by
  intros e i x
  induction e generalizing i with
  | bvar| lit| unit| loc| alloc₁| alloc₂| load₁| load₂| store₁| store₂ => simp
  | fvar y =>
    by_cases HEq : x = y
    . simp [if_pos HEq]
    . simp [if_neg HEq]
  | lam _ IH
  | lift _ IH
  | lam𝕔 _ IH
  | code _ IH
  | reflect _ IH
  | run _ IH =>
    apply IH
  | app₁ _ _ IH₀ IH₁
  | app₂ _ _ IH₀ IH₁
  | lets _ _ IH₀ IH₁
  | lets𝕔 _ _ IH₀ IH₁ =>
    simp; rw [IH₀, IH₁]

lemma store_free.under_opening_value : ∀ e v i, store_free v → store_free e → store_free (opening i v e) :=
  by
  intros e v i Hsf₀ Hsf₁
  induction e generalizing i with
  | alloc₁| alloc₂| load₁| load₂| store₁| store₂ => nomatch Hsf₁
  | fvar| lit| unit| loc => simp
  | bvar j =>
    by_cases HEq : j = i
    . simp [if_pos HEq]
      apply Hsf₀
    . simp [if_neg HEq]
  | lam _ IH
  | lift _ IH
  | lam𝕔 _ IH
  | code _ IH
  | reflect _ IH
  | run _ IH =>
    apply IH; apply Hsf₁
  | app₁ _ _ IH₀ IH₁
  | app₂ _ _ IH₀ IH₁
  | lets _ _ IH₀ IH₁
  | lets𝕔 _ _ IH₀ IH₁ =>
    constructor
    . apply IH₀; apply Hsf₁.left
    . apply IH₁; apply Hsf₁.right

lemma store_free.under_codify : ∀ e i, store_free e ↔ store_free (codify i e) :=
  by
  intros e i
  induction e generalizing i with
  | fvar| lit| unit| loc| alloc₁| alloc₂| load₁| load₂| store₁| store₂ => simp
  | bvar j =>
    by_cases HEq : j = i
    . simp [if_pos HEq]
    . simp [if_neg HEq]
  | lam _ IH
  | lift _ IH
  | lam𝕔 _ IH
  | code _ IH
  | reflect _ IH
  | run _ IH =>
    apply IH
  | app₁ _ _ IH₀ IH₁
  | app₂ _ _ IH₀ IH₁
  | lets _ _ IH₀ IH₁
  | lets𝕔 _ _ IH₀ IH₁ =>
    simp [← IH₀, ← IH₁]
