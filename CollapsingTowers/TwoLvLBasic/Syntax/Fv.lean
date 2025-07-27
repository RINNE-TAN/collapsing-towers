import Mathlib.Data.Set.Insert
import CollapsingTowers.TwoLvLBasic.Syntax.SyntacticTrans

@[simp]
def fv : Expr → Set ℕ
  | .bvar _ => ∅
  | .fvar x => { x }
  | .lam e => fv e
  | .lift e => fv e
  | .app₁ f arg => fv f ∪ fv arg
  | .app₂ f arg => fv f ∪ fv arg
  | .lit _ => ∅
  | .run e => fv e
  | .code e => fv e
  | .reflect e => fv e
  | .lam𝕔 e => fv e
  | .lets b e => fv b ∪ fv e
  | .lets𝕔 b e => fv b ∪ fv e

lemma fv.under_opening : ∀ i v e, fv (opening i v e) ⊆ fv v ∪ fv e :=
  by
  intros i v e
  induction e generalizing i with
  | bvar j =>
    simp; by_cases HEq : j = i
    . rw [if_pos HEq]
    . rw [if_neg HEq]; simp
  | fvar z => simp
  | lit => simp
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
    simp; constructor
    apply Set.Subset.trans; apply IH₀
    apply Set.union_subset_union; rfl; simp
    apply Set.Subset.trans; apply IH₁
    apply Set.union_subset_union; rfl; simp

lemma fv.not_in_under_opening :
  ∀ x y i e,
    x ∉ fv e →
    x ≠ y →
    x ∉ fv ({i ↦ y} e) :=
  by
  intros x y i e HNotIn HNe HIn
  apply HNotIn
  have H : fv ({i ↦ y} e) ⊆ { y } ∪ fv e := by apply fv.under_opening
  rw [Set.subset_def] at H
  cases (H x HIn)
  case inl => simp at *; omega
  case inr => assumption

lemma fv.not_in_under_subst :
  ∀ x e v,
    x ∉ fv v →
    x ∉ fv (subst x v e) :=
  by
  intros x e v HNotIn HIn
  apply HNotIn
  induction e with
  | bvar j => nomatch HIn
  | fvar y =>
    by_cases HEq : x = y
    . simp [if_pos HEq] at HIn
      apply HIn
    . simp [if_neg HEq] at HIn
      contradiction
  | lit => nomatch HIn
  | lam _ IH
  | lift _ IH
  | lam𝕔 _ IH
  | code _ IH
  | reflect _ IH
  | run _ IH =>
    apply IH; apply HIn
  | app₁ _ _ IH₀ IH₁
  | app₂ _ _ IH₀ IH₁
  | lets _ _ IH₀ IH₁
  | lets𝕔 _ _ IH₀ IH₁ =>
    simp at HIn
    cases HIn
    case inl HIn =>
      apply IH₀; apply HIn
    case inr HIn =>
      apply IH₁; apply HIn

lemma fv.under_closing : ∀ i x e, fv (closing i x e) = fv e \ { x } :=
  by
  intros i x e
  induction e generalizing i with
  | bvar => simp
  | fvar y =>
    simp; by_cases HEq : x = y
    . rw [if_pos HEq]
      rw [HEq]; simp
    . rw [if_neg HEq]
      rw [Set.diff_singleton_eq_self]
      rfl; apply HEq
  | lit => simp
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
    rw [Set.union_diff_distrib]
