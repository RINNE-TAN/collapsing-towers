
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
  .rep₂ (.arrow .nat .nat)

example : typing .fst [] expr₀ τ := by
  rw [expr₀, x₀, τ]
  repeat constructor

example : typing .fst [] expr₁ τ := by
  rw [expr₁, x₀, τ]
  repeat constructor

example : typing .fst [] expr₂ τ := by
  rw [expr₂, x₀, τ]
  repeat constructor

example : typing .fst [] expr₃ τ := by
  rw [expr₃, x₀, x₁, τ]
  apply typing.lift_code
  apply typing.lam𝕔
  apply typing.let𝕔
  repeat constructor

example : typing .fst [] expr₄ τ := by
  rw [expr₄, x₀, x₁, τ]
  apply typing.lift_code
  apply typing.lam𝕔
  apply typing.let𝕔
  repeat constructor

example : typing .fst [] expr₅ τ := by
  rw [expr₅, x₀, x₁, x₂, τ]
  repeat constructor

example : typing .fst [] expr₆ τ := by
  rw [expr₆, x₀, x₁, x₂, τ]
  apply typing.lift_code
  apply typing.lam𝕔
  apply typing.let𝕔
  repeat constructor

example : typing .fst [] expr₇ τ := by
  rw [expr₇, x₀, x₁, x₂, τ]
  repeat constructor

example : typing .fst [] expr₈ τ := by
  rw [expr₈, x₀, x₁, x₂, τ]
  repeat constructor

example : typing .fst [] expr₉ τ := by
  rw [expr₉, x₀, x₁, x₂, τ]
  repeat constructor

example : typing .fst [] expr𝕩 τ := by
  rw [expr𝕩, x₀, x₁, x₂, τ]
  apply typing.code₂
  apply typing.lets _ _ _ _ (.arrow .nat .nat)
  repeat constructor

end Example1

namespace PCP_Stuck

example : ∀ 𝕊 b τ, ¬typing 𝕊 [] (.let𝕔 b (.bvar 0)) τ :=
  by
  intros 𝕊 b τ Hτ
  cases Hτ <;> contradiction

end PCP_Stuck
