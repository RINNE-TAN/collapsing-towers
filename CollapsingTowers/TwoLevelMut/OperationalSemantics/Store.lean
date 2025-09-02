import CollapsingTowers.TwoLevelMut.Utils.Defs
import CollapsingTowers.TwoLevelMut.Syntax.Defs

abbrev Store :=
  List Expr

inductive ok : Store → Prop
  | nil : ok []
  | cons : ∀ n σ, ok σ → ok (.lit n :: σ)

lemma ok.binds : ∀ σ l v, ok σ → binds l v σ → ∃ n, .lit n = v :=
  by
  intros σ l v Hok Hbinds
  induction Hok
  case nil => contradiction
  case cons n σ Hok IH =>
    by_cases HEq : σ.length = l
    . simp [if_pos HEq] at Hbinds
      exists n
    . simp [if_neg HEq] at Hbinds
      apply IH Hbinds

lemma ok.patch :
  ∀ l n σ₀ σ₁,
    patch l (.lit n) σ₀ σ₁ →
    ok σ₀ →
    ok σ₁ :=
  by
  intros l n σ₀ σ₁ Hpatch Hok₀
  induction Hok₀ generalizing σ₁
  case nil =>
    have HEq := patch.length _ _ _ _ Hpatch
    symm at HEq; simp at HEq; simp [HEq]
    apply ok.nil
  case cons head₀ tails₀ Hok₀ IH =>
    cases σ₁
    case nil => apply ok.nil
    case cons head₁ tails₁ =>
      by_cases HEq : tails₀.length = l
      . simp [if_pos HEq] at Hpatch
        simp [← Hpatch]
        apply ok.cons _ _ Hok₀
      . simp [if_neg HEq] at Hpatch
        generalize HEq : setr l (.lit n) tails₀ = tailRes
        cases tailRes with
        | none => simp [HEq] at Hpatch
        | some tails₁ =>
          simp [HEq] at Hpatch
          simp [← Hpatch]
          apply ok.cons _ _ (IH _ HEq)
