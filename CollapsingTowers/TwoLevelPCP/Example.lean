
import Mathlib.Data.Finset.Basic
import CollapsingTowers.TwoLevelPCP.SmallStep
import CollapsingTowers.TwoLevelPCP.Typing
namespace Example1

/-- Example 1:
lift x. x +₂ (x +₂ x)
→⋆
code {
  lets f = lam₁ x.
    lets y = x + x in
    lets z = x + y in z
  in f
}
-/
def x₀ : Expr :=
  .fvar 0

def x₁ : Expr :=
  .fvar 1

def x₂ : Expr :=
  .fvar 2

def x₃ : Expr :=
  .fvar 3

def expr₀ : Expr :=
  .lift (.lam₁ (close₀ 0 (.plus₂ x₀ (.plus₂ x₀ x₀))))

def expr₁ : Expr :=
  .lam𝕔 (close₀ 0 (.plus₂ (.code x₀) (.plus₂ (.code x₀) (.code x₀))))

def expr₂ : Expr :=
  .lam𝕔 (close₀ 0 (.plus₂ (.code x₀) (.reflect (.plus₁ x₀ x₀))))

def expr₃ : Expr :=
  .lam𝕔 (close₀ 0 (.let𝕔 (.plus₁ x₀ x₀) (close₀ 1 (.plus₂ (.code x₀) (.code x₁)))))

def expr₄ : Expr :=
  .lam𝕔 (close₀ 0 (.let𝕔 (.plus₁ x₀ x₀) (close₀ 1 (.reflect (.plus₁ x₀ x₁)))))

def expr₅ : Expr :=
  .lam𝕔 (close₀ 0 (.let𝕔 (.plus₁ x₀ x₀) (close₀ 1 (.let𝕔 (.plus₁ x₀ x₁) (close₀ 2 (.code x₂))))))

def expr₆ : Expr :=
  .lam𝕔 (close₀ 0 (.let𝕔 (.plus₁ x₀ x₀) (close₀ 1 (.code (.lets (.plus₁ x₀ x₁) (close₀ 2 x₂))))))

def expr₇ : Expr :=
  .lam𝕔 (close₀ 0 (.code (.lets (.plus₁ x₀ x₀) (close₀ 1 (.lets (.plus₁ x₀ x₁) (close₀ 2 x₂))))))

def expr₈ : Expr :=
  .reflect (.lam₁ (close₀ 0 (.lets (.plus₁ x₀ x₀) (close₀ 1 (.lets (.plus₁ x₀ x₁) (close₀ 2 x₂))))))

def expr₉ : Expr :=
  .let𝕔 (.lam₁ (close₀ 0 (.lets (.plus₁ x₀ x₀) (close₀ 1 (.lets (.plus₁ x₀ x₁) (close₀ 2 x₂)))))) (close₀ 3 (.code x₃))

def expr𝕩 : Expr :=
  .code (.lets (.lam₁ (close₀ 0 (.lets (.plus₁ x₀ x₀) (close₀ 1 (.lets (.plus₁ x₀ x₁) (close₀ 2 x₂)))))) (close₀ 3 x₃))

def τ : Ty :=
  .rep (.arrow .nat .nat ∅)

example : typing_reification [] expr₀ τ .reflect :=
  by
  rw [expr₀, x₀, τ]
  apply typing_reification.reflect
  apply typing.lift_lam
  apply typing.lam₁
  apply typing.plus₂
  apply typing.fvar; . repeat constructor
  apply typing.plus₂
  apply typing.fvar; . repeat constructor
  apply typing.fvar; . repeat constructor
  repeat constructor

example : typing_reification [] expr₁ τ .reflect :=
  by
  rw [expr₁, x₀, τ]
  apply typing_reification.reflect
  apply typing.lam𝕔
  apply typing_reification.reflect
  apply typing.plus₂
  apply typing.code₁; . repeat constructor
  apply typing.plus₂
  apply typing.code₁; . repeat constructor
  apply typing.code₁; . repeat constructor
  repeat constructor

example : typing_reification [] expr₂ τ .reflect :=
  by
  rw [expr₂, x₀, τ]
  apply typing_reification.reflect
  apply typing.lam𝕔
  apply typing_reification.reflect
  apply typing.plus₂
  apply typing.code₁; . repeat constructor
  apply typing.reflect; rw [← union_empty ∅]
  apply typing.plus₁
  apply typing.fvar; . repeat constructor
  apply typing.fvar; . repeat constructor
  repeat constructor

example : typing_reification [] expr₃ τ .reflect :=
  by
  rw [expr₃, x₀, x₁, τ]
  apply typing_reification.reflect
  apply typing.lam𝕔
  apply typing_reification.pure
  apply typing.let𝕔; rw [← union_empty ∅]
  apply typing.plus₁
  apply typing.fvar; . repeat constructor
  apply typing.fvar; . repeat constructor
  apply typing_reification.reflect
  apply typing.plus₂
  apply typing.code₁; . repeat constructor
  apply typing.code₁; . repeat constructor
  repeat constructor

example : typing_reification [] expr₄ τ .reflect :=
  by
  rw [expr₄, x₀, x₁, τ]
  apply typing_reification.reflect
  apply typing.lam𝕔
  apply typing_reification.pure
  apply typing.let𝕔; rw [← union_empty ∅]
  apply typing.plus₁
  apply typing.fvar; . repeat constructor
  apply typing.fvar; . repeat constructor
  apply typing_reification.reflect
  apply typing.reflect; rw [← union_empty ∅]
  apply typing.plus₁
  apply typing.fvar; . repeat constructor
  apply typing.fvar; . repeat constructor
  repeat constructor

example : typing_reification [] expr₅ τ .reflect :=
  by
  rw [expr₅, x₀, x₁, x₂, τ]
  apply typing_reification.reflect
  apply typing.lam𝕔
  apply typing_reification.pure
  apply typing.let𝕔; rw [← union_empty ∅]
  apply typing.plus₁
  apply typing.fvar; . repeat constructor
  apply typing.fvar; . repeat constructor
  apply typing_reification.pure
  apply typing.let𝕔; rw [← union_empty ∅]
  apply typing.plus₁
  apply typing.fvar; . repeat constructor
  apply typing.fvar; . repeat constructor
  apply typing_reification.pure
  apply typing.code₂
  apply typing.fvar; . repeat constructor
  repeat constructor

example : typing_reification [] expr₆ τ .reflect :=
  by
  rw [expr₆, x₀, x₁, x₂, τ]
  apply typing_reification.reflect
  apply typing.lam𝕔
  apply typing_reification.pure
  apply typing.let𝕔; rw [← union_empty ∅]
  apply typing.plus₁
  apply typing.fvar; . repeat constructor
  apply typing.fvar; . repeat constructor
  apply typing_reification.pure
  apply typing.code₂; rw [← union_empty ∅]
  apply typing.lets; rw [← union_empty ∅]
  apply typing.plus₁
  apply typing.fvar; . repeat constructor
  apply typing.fvar; . repeat constructor
  apply typing.fvar; . repeat constructor
  repeat constructor

example : typing_reification [] expr₇ τ .reflect :=
  by
  rw [expr₇, x₀, x₁, x₂, τ]
  apply typing_reification.reflect
  apply typing.lam𝕔
  apply typing_reification.pure
  apply typing.code₂; rw [← union_empty ∅]
  apply typing.lets; rw [← union_empty ∅]
  apply typing.plus₁
  apply typing.fvar; . repeat constructor
  apply typing.fvar; . repeat constructor
  rw [← union_empty ∅]
  apply typing.lets; rw [← union_empty ∅]
  apply typing.plus₁
  apply typing.fvar; . repeat constructor
  apply typing.fvar; . repeat constructor
  apply typing.fvar; . repeat constructor
  repeat constructor

example : typing_reification [] expr₈ τ .reflect :=
  by
  rw [expr₈, x₀, x₁, x₂, τ]
  apply typing_reification.reflect
  apply typing.reflect
  apply typing.lam₁; rw [← union_empty ∅]
  apply typing.lets; rw [← union_empty ∅]
  apply typing.plus₁
  apply typing.fvar; . repeat constructor
  apply typing.fvar; . repeat constructor
  rw [← union_empty ∅]
  apply typing.lets; rw [← union_empty ∅]
  apply typing.plus₁
  apply typing.fvar; . repeat constructor
  apply typing.fvar; . repeat constructor
  apply typing.fvar; . repeat constructor
  repeat constructor

example : typing_reification [] expr₉ τ .pure :=
  by
  rw [expr₉, x₀, x₁, x₂, τ]
  apply typing_reification.pure
  apply typing.let𝕔
  apply typing.lam₁
  apply typing.lets
  apply typing.plus₁
  apply typing.fvar; . repeat constructor
  apply typing.fvar; . repeat constructor
  apply typing.lets
  apply typing.plus₁
  apply typing.fvar; . repeat constructor
  apply typing.fvar; . repeat constructor
  apply typing.fvar; . repeat constructor
  repeat constructor

example : typing_reification [] expr𝕩 τ .pure :=
  by
  rw [expr𝕩, x₀, x₁, x₂, τ]
  apply typing_reification.pure
  apply typing.code₂; rw [← union_empty ∅]
  apply typing.lets; rw [← union_empty ∅]
  apply typing.lam₁
  apply typing.lets
  apply typing.plus₁
  apply typing.fvar; . repeat constructor
  apply typing.fvar; . repeat constructor
  apply typing.lets
  apply typing.plus₁
  apply typing.fvar; . repeat constructor
  apply typing.fvar; . repeat constructor
  apply typing.fvar; . repeat constructor
  repeat constructor

end Example1

namespace PhaseConsistency

-- stuck example
-- letc x (* phase 2 *) = eff in
-- x (* phase 1 *)
example : ∀ b τ φ, ¬typing_reification [] (.let𝕔 b (.bvar 0)) τ φ :=
  by
  intros _ _ _ Hτ
  cases Hτ <;> contradiction

-- cross stage persistence
-- let x (* phase 1 *) = ref 0 in
-- code x (* phase 2 *)
example : ∀ b τ φ, ¬typing_reification [] (.lets b (.code (.bvar 0))) τ φ :=
  by
  intros _ _ _ Hτ
  cases Hτ
  case pure Hτ =>
    generalize eqφ : (∅ : Effects) = φ
    rw [eqφ] at Hτ
    cases Hτ; contradiction
  case reflect Hτ =>
    generalize eqφ : (.reflect : Effects) = φ
    rw [eqφ] at Hτ
    cases Hτ; contradiction

end PhaseConsistency

namespace Reification

-- reify under B context
-- let x =
--    letc x0 = eff in
--    code x0
-- in e
example : ∀ b e τ, ¬typing_reification [] (.lets (.let𝕔 b (.code (.bvar 0))) e) τ φ :=
  by
  intros _ _ _ Hτ
  cases Hτ
  case pure Hτ =>
    generalize eqφ : (∅ : Effects) = φ
    rw [eqφ] at Hτ
    cases Hτ
    case lets Hcode _ _ => cases Hcode; contradiction
  case reflect Hτ =>
    generalize eqφ : (.reflect : Effects) = φ
    rw [eqφ] at Hτ
    cases Hτ
    case lets Hcode _ _ => cases Hcode; contradiction

-- reify result under B context
-- let x = code {
--    let x0 = eff in
--    x0
-- }
-- in e
example : ∀ b e τ φ, ¬typing_reification [] (.lets (.code (.lets b (.bvar 0))) e) τ φ :=
  by
  intros _ _ _ _ Hτ
  cases Hτ
  case pure Hτ =>
    generalize eqφ : (∅ : Effects) = φ
    rw [eqφ] at Hτ
    cases Hτ
    case lets Hcode _ _ => cases Hcode; contradiction
  case reflect Hτ =>
    generalize eqφ : (.reflect : Effects) = φ
    rw [eqφ] at Hτ
    cases Hτ
    case lets Hcode _ _ => cases Hcode; contradiction

-- E context must has
-- E ~ fragment τ -> rep τ
-- let x = reflect e
-- in 1
example : ∀ e τ φ, ¬typing_reification [] (.lets (.reflect e) (.lit₁ 1)) τ φ :=
  by
  intros _ _ _ Hτ
  cases Hτ
  case pure Hτ =>
    generalize eqφ : (∅ : Effects) = φ
    rw [eqφ] at Hτ
    cases Hτ
    case lets Hreflect _ _ =>
      cases Hreflect
      simp at eqφ
  case reflect Hτ =>
    generalize eqφ : (.reflect : Effects) = φ
    rw [eqφ] at Hτ
    cases Hτ
    case lets Hreflect _ _ => cases Hreflect; contradiction

end Reification
