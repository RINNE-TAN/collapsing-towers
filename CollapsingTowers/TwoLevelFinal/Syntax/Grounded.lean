import CollapsingTowers.TwoLevelFinal.Syntax.Transform

@[simp]
def grounded (e : Expr) : Prop :=
  match e with
  | .bvar _ => true
  | .fvar _ => true
  | .lam e => grounded e
  | .lift _ => false
  | .app₁ f arg => grounded f ∧ grounded arg
  | .app₂ _ _ => false
  | .binary₁ _ l r => grounded l ∧ grounded r
  | .binary₂ _ _ _ => false
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
  | .fix₁ e => grounded e
  | .fix₂ _ => false
  | .ifz₁ c l r => grounded c ∧ grounded l ∧ grounded r
  | .ifz₂ _ _ _ => false

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
  | load₂ _ IH
  | fix₁ _ IH
  | fix₂ _ IH =>
    simp [IH]
  | app₁ _ _ IH₀ IH₁
  | app₂ _ _ IH₀ IH₁
  | store₁ _ _ IH₀ IH₁
  | store₂ _ _ IH₀ IH₁
  | binary₁ _ _ _ IH₀ IH₁
  | binary₂ _ _ _ IH₀ IH₁
  | lets _ _ IH₀ IH₁
  | lets𝕔 _ _ IH₀ IH₁ =>
    simp [IH₀, IH₁]
  | ifz₁ _ _ _ IH₀ IH₁ IH₂
  | ifz₂ _ _ _ IH₀ IH₁ IH₂ =>
    simp [IH₀, IH₁, IH₂]

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
  | bvar| fvar| app₂| binary₂| lit| lam𝕔| lets𝕔| unit| loc| alloc₂| load₂| store₂| fix₂| ifz₂ => simp
  | lam _ IH
  | alloc₁ _ IH
  | load₁ _ IH
  | fix₁ _ IH =>
    simp [IH]
  | app₁ _ _ IH₀ IH₁
  | binary₁ _ _ _ IH₀ IH₁
  | lets _ _ IH₀ IH₁
  | store₁ _ _ IH₀ IH₁ =>
    simp [IH₀, IH₁]
  | ifz₁ _ _ _ IH₀ IH₁ IH₂ =>
    simp [IH₀, IH₁, IH₂]
  | lift => simp; apply erasable.lift
  | run => simp; apply erasable.run
  | code => simp; apply erasable.code
  | reflect => simp; apply erasable.reflect

lemma grounded.under_opening : ∀ e i x, grounded e ↔ grounded ({i ↦ x} e) :=
  by
  intros e i x
  induction e generalizing i with
  | fvar| app₂| binary₂| lit| lam𝕔| lets𝕔| lift| run| code| reflect| unit| loc| alloc₂| load₂| store₂| fix₂| ifz₂ => simp
  | bvar j =>
    by_cases HEq : j = i
    . simp [if_pos HEq]
    . simp [if_neg HEq]
  | lam _ IH
  | alloc₁ _ IH
  | load₁ _ IH
  | fix₁ _ IH =>
    apply IH
  | app₁ _ _ IH₀ IH₁
  | binary₁ _ _ _ IH₀ IH₁
  | store₁ _ _ IH₀ IH₁
  | lets _ _ IH₀ IH₁ =>
    simp; rw [IH₀, IH₁]
  | ifz₁ _ _ _ IH₀ IH₁ IH₂ =>
    simp; rw [IH₀, IH₁, IH₂]

lemma grounded.under_subst : ∀ e v x, grounded v → grounded e → grounded (subst x v e) :=
  by
  intros e v x
  induction e with
  | bvar| app₂| binary₂| lit| lam𝕔| lets𝕔| lift| run| code| reflect| unit| loc| alloc₂| load₂| store₂| fix₂| ifz₂ => simp
  | fvar y =>
    intros Hv
    by_cases HEq : x = y
    . simp [if_pos HEq, Hv]
    . simp [if_neg HEq]
  | lam _ IH
  | alloc₁ _ IH
  | load₁ _ IH
  | fix₁ _ IH =>
    apply IH
  | app₁ _ _ IH₀ IH₁
  | binary₁ _ _ _ IH₀ IH₁
  | store₁ _ _ IH₀ IH₁
  | lets _ _ IH₀ IH₁ =>
    simp; intros Hv H₀ H₁; constructor
    apply IH₀; apply Hv; apply H₀
    apply IH₁; apply Hv; apply H₁
  | ifz₁ _ _ _ IH₀ IH₁ IH₂ =>
    simp; intros Hv H₀ H₁ H₂; constructor
    apply IH₀; apply Hv; apply H₀; constructor
    apply IH₁; apply Hv; apply H₁
    apply IH₂; apply Hv; apply H₂

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
  | fvar| app₂| binary₂| lit| lam𝕔| lets𝕔| lift| run| code| reflect| unit| loc| alloc₂| load₂| store₂| fix₂| ifz₂ => simp
  | bvar j =>
    simp; intros Hv
    by_cases HEq : j = i
    . simp [if_pos HEq, Hv]
    . simp [if_neg HEq]
  | lam _ IH
  | alloc₁ _ IH
  | load₁ _ IH
  | fix₁ _ IH =>
    apply IH
  | app₁ _ _ IH₀ IH₁
  | binary₁ _ _ _ IH₀ IH₁
  | store₁ _ _ IH₀ IH₁
  | lets _ _ IH₀ IH₁ =>
    simp; intros Hv H₀ H₁; constructor
    apply IH₀; apply Hv; apply H₀
    apply IH₁; apply Hv; apply H₁
  | ifz₁ _ _ _ IH₀ IH₁ IH₂ =>
    simp; intros Hv H₀ H₁ H₂; constructor
    apply IH₀; apply Hv; apply H₀; constructor
    apply IH₁; apply Hv; apply H₁
    apply IH₂; apply Hv; apply H₂

@[simp]
def immut (e : Expr) : Prop :=
  match e with
  | .bvar _ => true
  | .fvar _ => true
  | .lam e => immut e
  | .lift e => immut e
  | .app₁ f arg => immut f ∧ immut arg
  | .app₂ f arg => immut f ∧ immut arg
  | .binary₁ _ l r => immut l ∧ immut r
  | .binary₂ _ l r => immut l ∧ immut r
  | .lit _ => true
  | .run e => immut e
  | .code e => immut e
  | .reflect e => immut e
  | .lam𝕔 e => immut e
  | .lets b e => immut b ∧ immut e
  | .lets𝕔 b e => immut b ∧ immut e
  | .unit => true
  | .loc _ => true
  | .alloc₁ _ => false
  | .alloc₂ _ => false
  | .load₁ _ => false
  | .load₂ _ => false
  | .store₁ _ _ => false
  | .store₂ _ _ => false
  | .fix₁ e => immut e
  | .fix₂ e => immut e
  | .ifz₁ c l r => immut c ∧ immut l ∧ immut r
  | .ifz₂ c l r => immut c ∧ immut l ∧ immut r

lemma immut.under_opening : ∀ e i x, immut e ↔ immut ({i ↦ x} e) :=
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
  | run _ IH
  | fix₁ _ IH
  | fix₂ _ IH =>
    apply IH
  | app₁ _ _ IH₀ IH₁
  | app₂ _ _ IH₀ IH₁
  | binary₁ _ _ _ IH₀ IH₁
  | binary₂ _ _ _ IH₀ IH₁
  | lets _ _ IH₀ IH₁
  | lets𝕔 _ _ IH₀ IH₁ =>
    simp; rw [IH₀, IH₁]
  | ifz₁ _ _ _ IH₀ IH₁ IH₂
  | ifz₂ _ _ _ IH₀ IH₁ IH₂ =>
    simp; rw [IH₀, IH₁, IH₂]

lemma immut.under_closing : ∀ e i x, immut e ↔ immut ({i ↤ x} e) :=
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
  | run _ IH
  | fix₁ _ IH
  | fix₂ _ IH =>
    apply IH
  | app₁ _ _ IH₀ IH₁
  | app₂ _ _ IH₀ IH₁
  | binary₁ _ _ _ IH₀ IH₁
  | binary₂ _ _ _ IH₀ IH₁
  | lets _ _ IH₀ IH₁
  | lets𝕔 _ _ IH₀ IH₁ =>
    simp; rw [IH₀, IH₁]
  | ifz₁ _ _ _ IH₀ IH₁ IH₂
  | ifz₂ _ _ _ IH₀ IH₁ IH₂ =>
    simp; rw [IH₀, IH₁, IH₂]

lemma immut.under_opening_value : ∀ e v i, immut v → immut e → immut (opening i v e) :=
  by
  intros e v i Himmut₀ Himmut₁
  induction e generalizing i with
  | alloc₁| alloc₂| load₁| load₂| store₁| store₂ => nomatch Himmut₁
  | fvar| lit| unit| loc => simp
  | bvar j =>
    by_cases HEq : j = i
    . simp [if_pos HEq]
      apply Himmut₀
    . simp [if_neg HEq]
  | lam _ IH
  | lift _ IH
  | lam𝕔 _ IH
  | code _ IH
  | reflect _ IH
  | run _ IH
  | fix₁ _ IH
  | fix₂ _ IH =>
    apply IH; apply Himmut₁
  | app₁ _ _ IH₀ IH₁
  | app₂ _ _ IH₀ IH₁
  | binary₁ _ _ _ IH₀ IH₁
  | binary₂ _ _ _ IH₀ IH₁
  | lets _ _ IH₀ IH₁
  | lets𝕔 _ _ IH₀ IH₁ =>
    constructor
    . apply IH₀; apply Himmut₁.left
    . apply IH₁; apply Himmut₁.right
  | ifz₁ _ _ _ IH₀ IH₁ IH₂
  | ifz₂ _ _ _ IH₀ IH₁ IH₂ =>
    constructor
    . apply IH₀; apply Himmut₁.left
    constructor
    . apply IH₁; apply Himmut₁.right.left
    . apply IH₂; apply Himmut₁.right.right

lemma immut.under_codify : ∀ e i, immut e ↔ immut (codify i e) :=
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
  | run _ IH
  | fix₁ _ IH
  | fix₂ _ IH =>
    apply IH
  | app₁ _ _ IH₀ IH₁
  | app₂ _ _ IH₀ IH₁
  | binary₁ _ _ _ IH₀ IH₁
  | binary₂ _ _ _ IH₀ IH₁
  | lets _ _ IH₀ IH₁
  | lets𝕔 _ _ IH₀ IH₁ =>
    simp [← IH₀, ← IH₁]
  | ifz₁ _ _ _ IH₀ IH₁ IH₂
  | ifz₂ _ _ _ IH₀ IH₁ IH₂ =>
    simp [← IH₀, ← IH₁, ← IH₂]
