
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

def ty : Ty :=
  .rep₂ (.arrow .nat .nat)

example : typing .snd [] expr₀ ty := by
  rw [expr₀, x₀, ty]
  repeat constructor

example : typing .snd [] expr₁ ty := by
  rw [expr₁, x₀, ty]
  repeat constructor

example : typing .snd [] expr₂ ty := by
  rw [expr₂, x₀, ty]
  repeat constructor

example : typing .snd [] expr₃ ty := by
  rw [expr₃, x₀, x₁, ty]
  apply typing.lift_code
  apply typing.lam𝕔
  apply typing.let𝕔
  repeat constructor

example : typing .snd [] expr₄ ty := by
  rw [expr₄, x₀, x₁, ty]
  apply typing.lift_code
  apply typing.lam𝕔
  apply typing.let𝕔
  repeat constructor

example : typing .snd [] expr₅ ty := by
  rw [expr₅, x₀, x₁, x₂, ty]
  apply typing.lift_code
  apply typing.lam𝕔
  repeat
    ( apply typing.let𝕔 _ _ _ .nat
      apply typing.plus₁
      apply typing.fvar; simp
      apply typing.fvar; simp)
  repeat constructor

example : typing .snd [] expr₆ ty := by
  rw [expr₆, x₀, x₁, x₂, ty]
  apply typing.lift_code
  apply typing.lam𝕔
  apply typing.let𝕔
  repeat constructor

example : typing .snd [] expr₇ ty := by
  rw [expr₇, x₀, x₁, x₂, ty]
  repeat constructor

example : typing .snd [] expr₈ ty := by
  rw [expr₈, x₀, x₁, x₂, ty]
  repeat constructor

example : typing .snd [] expr₉ ty := by
  rw [expr₉, x₀, x₁, x₂, ty]
  apply typing.let𝕔 _ _ _ (.arrow .nat .nat)
  repeat constructor

example : typing .snd [] expr𝕩 ty := by
  rw [expr𝕩, x₀, x₁, x₂, ty]
  apply typing.code₂
  apply typing.lets _ _ _ _ (.arrow .nat .nat)
  repeat constructor

end Example1
