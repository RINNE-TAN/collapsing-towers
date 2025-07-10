
import CollapsingTowers.TwoLevelFull.Typing
namespace PhaseConsistency

-- stuck example
-- letc x (* phase 2 *) = eff in
-- x (* phase 1 *)
example : ∀ b τ φ, ¬typing_reification [] [] (.let𝕔 b (.bvar 0)) τ φ :=
  by
  intros _ _ _ Hτ
  cases Hτ <;> contradiction

-- cross stage persistence
-- let x (* phase 1 *) = ref 0 in
-- code x (* phase 2 *)
example : ∀ b τ φ, ¬typing_reification [] [] (.lets b (.code (.bvar 0))) τ φ :=
  by
  intros _ _ _ Hτ
  cases Hτ
  case pure Hτ =>
    generalize HEqφ : (∅ : Effects) = φ
    rw [HEqφ] at Hτ
    cases Hτ; contradiction
  case reify Hτ =>
    cases Hτ; contradiction

end PhaseConsistency

namespace Reification

-- reify under B context
-- let x =
--    letc x0 = eff in
--    code x0
-- in e
example : ∀ b e τ φ, ¬typing_reification [] [] (.lets (.let𝕔 b (.code (.bvar 0))) e) τ φ :=
  by
  intros _ _ _ _ Hτ
  cases Hτ
  case pure Hτ =>
    generalize HEqφ : (∅ : Effects) = φ
    rw [HEqφ] at Hτ
    cases Hτ
    case lets Hcode _ _ => cases Hcode; contradiction
  case reify Hτ =>
    cases Hτ
    case lets Hcode _ _ => cases Hcode; contradiction

-- reify result under B context
-- let x = code (
--    let x0 = eff in
--    x0
-- )
-- in e
example : ∀ b e τ φ, ¬typing_reification [] [] (.lets (.code (.lets b (.bvar 0))) e) τ φ :=
  by
  intros _ _ _ _ Hτ
  cases Hτ
  case pure Hτ =>
    generalize HEqφ : (∅ : Effects) = φ
    rw [HEqφ] at Hτ
    cases Hτ
    case lets Hcode _ _ => cases Hcode; contradiction
  case reify Hτ =>
    cases Hτ
    case lets Hcode _ _ => cases Hcode; contradiction

-- E context must has
-- E ~ fragment τ -> rep τ
-- let x = reflect e
-- in 1
example : ∀ e τ φ, ¬typing_reification [] [] (.lets (.reflect e) (.lit 1)) τ φ :=
  by
  intros _ _ _ Hτ
  cases Hτ
  case pure Hτ =>
    generalize HEqφ : (∅ : Effects) = φ
    rw [HEqφ] at Hτ
    cases Hτ
    case lets Hreflect _ _ =>
      cases Hreflect
      simp at HEqφ
  case reify Hτ =>
    cases Hτ
    contradiction

end Reification
