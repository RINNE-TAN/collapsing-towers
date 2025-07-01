
import CollapsingTowers.TwoLevelPCP.Typing
namespace Fig4
-- Fig. 4. Example of small-step derivation in λ↑↓
-- lift (λx . x +₂ (x *₂ x))  -->⋆
-- code (
--   lets f = λx₀.
--     lets x₁ = x₀ * x₀ in
--     lets x₂ = x₀ + x₁ in
--     x₂
--   in f
-- )
def x₀ : Expr :=
  .fvar 0

def x₁ : Expr :=
  .fvar 1

def x₂ : Expr :=
  .fvar 2

def f : Expr :=
  .fvar 3

def expr₀ : Expr :=
  .lift (
    .lam (close₀ 0 (
      .binary₂ .add x₀ (.binary₂ .mul x₀ x₀))))

def expr₁ : Expr :=
  .lam𝕔 (close₀ 0 (
    .binary₂ .add (.code x₀) (.binary₂ .mul (.code x₀) (.code x₀))))

def expr₂ : Expr :=
  .lam𝕔 (close₀ 0 (
    .binary₂ .add (.code x₀) (.reflect (.binary₁ .mul x₀ x₀))))

def expr₃ : Expr :=
  .lam𝕔 (close₀ 0 (
    .let𝕔 (.binary₁ .mul x₀ x₀) (close₀ 1 (
    .binary₂ .add (.code x₀) (.code x₁)))))

def expr₄ : Expr :=
  .lam𝕔 (close₀ 0 (
    .let𝕔 (.binary₁ .mul x₀ x₀) (close₀ 1 (
    .reflect (.binary₁ .add x₀ x₁)))))

def expr₅ : Expr :=
  .lam𝕔 (close₀ 0 (
    .let𝕔 (.binary₁ .mul x₀ x₀) (close₀ 1 (
    .let𝕔 (.binary₁ .add x₀ x₁) (close₀ 2 (
    .code x₂))))))

def expr₆ : Expr :=
  .lam𝕔 (close₀ 0 (
    .let𝕔 (.binary₁ .mul x₀ x₀) (close₀ 1 (
    .code (
      .lets (.binary₁ .add x₀ x₁) (close₀ 2
      x₂))))))

def expr₇ : Expr :=
  .lam𝕔 (close₀ 0 (
    .code (
      .lets (.binary₁ .mul x₀ x₀) (close₀ 1 (
      .lets (.binary₁ .add x₀ x₁) (close₀ 2
      x₂))))))

def expr₈ : Expr :=
  .reflect (
    .lam (close₀ 0 (
      .lets (.binary₁ .mul x₀ x₀) (close₀ 1 (
      .lets (.binary₁ .add x₀ x₁) (close₀ 2
      x₂))))))

def expr₉ : Expr :=
  .let𝕔 (
    .lam (close₀ 0 (
      .lets (.binary₁ .mul x₀ x₀) (close₀ 1 (
      .lets (.binary₁ .add x₀ x₁) (close₀ 2
      x₂)))))) (close₀ 3 (
  .code f))

def expr𝕩 : Expr :=
  .code (
    .lets (
      .lam (close₀ 0 (
        .lets (.binary₁ .mul x₀ x₀) (close₀ 1 (
        .lets (.binary₁ .add x₀ x₁) (close₀ 2
        x₂)))))) (close₀ 3
    f))

example : step ([], expr₀) ([], expr₁) := by
  apply step_lvl.step𝕄 _ _ _ _ ctx𝕄.hole
  repeat constructor

example : step ([], expr₁) ([], expr₂) := by
  apply step_lvl.step𝕄 _ _ _ _ (ctx𝕄.consℝ _ _ ctxℝ.lam𝕔 (ctx𝕄.cons𝔹 _ _ (ctx𝔹.binaryr₂ _ _ _) ctx𝕄.hole))
  repeat constructor

example : step ([], expr₂) ([], expr₃) := by
  apply step_lvl.reflect _ _ _ _ (ctxℙ.consℚ _ (ctxℚ.holeℝ _ ctxℝ.lam𝕔)) (ctx𝔼.cons𝔹 _ _ (ctx𝔹.binaryr₂ _ _ _) ctx𝔼.hole)
  repeat constructor

example : step ([], expr₃) ([], expr₄) := by
  apply step_lvl.step𝕄 _ _ _ _ (ctx𝕄.consℝ _ _ ctxℝ.lam𝕔 (ctx𝕄.consℝ _ _ (ctxℝ.let𝕔 _ _) ctx𝕄.hole))
  repeat constructor

example : step ([], expr₄) ([], expr₅) := by
  apply step_lvl.reflect _ _ _ _ (ctxℙ.consℚ _ (ctxℚ.consℝ _ _ ctxℝ.lam𝕔 (ctxℚ.holeℝ _ (ctxℝ.let𝕔 _ _)))) ctx𝔼.hole
  repeat constructor

example : step ([], expr₅) ([], expr₆) := by
  apply step_lvl.step𝕄 _ _ _ _ (ctx𝕄.consℝ _ _ ctxℝ.lam𝕔 (ctx𝕄.consℝ _ _ (ctxℝ.let𝕔 _ _) ctx𝕄.hole))
  repeat constructor

example : step ([], expr₆) ([], expr₇) := by
  apply step_lvl.step𝕄 _ _ _ _ (ctx𝕄.consℝ _ _ ctxℝ.lam𝕔 ctx𝕄.hole)
  repeat constructor

example : step ([], expr₇) ([], expr₈) := by
  simp; apply step_lvl.step𝕄 _ _ _ _ ctx𝕄.hole
  repeat constructor

example : step ([], expr₈) ([], expr₉) := by
  apply step_lvl.reflect _ _ _ _ ctxℙ.hole ctx𝔼.hole
  repeat constructor

example : step ([], expr₉) ([], expr𝕩) := by
  apply step_lvl.step𝕄 _ _ _ _ ctx𝕄.hole
  repeat constructor

def τ : Ty :=
  .rep (.arrow .nat .nat ∅)

example : typing_reification [] [] expr₀ τ .reify :=
  by
  rw [expr₀, x₀, τ]
  apply typing_reification.reify
  apply typing.lift_lam
  apply typing.lam
  apply typing.binary₂
  apply typing.fvar; repeat simp
  apply typing.binary₂
  apply typing.fvar; repeat simp
  apply typing.fvar; repeat simp

example : typing_reification [] [] expr₁ τ .reify :=
  by
  rw [expr₁, x₀, τ]
  apply typing_reification.reify
  apply typing.lam𝕔
  apply typing_reification.reify
  apply typing.binary₂
  apply typing.code_fragment; repeat simp
  apply typing.binary₂
  apply typing.code_fragment; repeat simp
  apply typing.code_fragment; repeat simp

example : typing_reification [] [] expr₂ τ .reify :=
  by
  rw [expr₂, x₀, τ]
  apply typing_reification.reify
  apply typing.lam𝕔
  apply typing_reification.reify
  apply typing.binary₂
  apply typing.code_fragment; repeat simp
  apply typing.reflect; rw [← union_pure_left ∅]
  apply typing.binary₁
  apply typing.fvar; repeat simp
  apply typing.fvar; repeat simp

example : typing_reification [] [] expr₃ τ .reify :=
  by
  rw [expr₃, x₀, x₁, τ]
  apply typing_reification.reify
  apply typing.lam𝕔
  apply typing_reification.pure
  apply typing.let𝕔; rw [← union_pure_left ∅]
  apply typing.binary₁
  apply typing.fvar; repeat simp
  apply typing.fvar; repeat simp
  apply typing_reification.reify
  apply typing.binary₂
  apply typing.code_fragment; repeat simp
  apply typing.code_fragment; repeat simp

example : typing_reification [] [] expr₄ τ .reify :=
  by
  rw [expr₄, x₀, x₁, τ]
  apply typing_reification.reify
  apply typing.lam𝕔
  apply typing_reification.pure
  apply typing.let𝕔; rw [← union_pure_left ∅]
  apply typing.binary₁
  apply typing.fvar; repeat simp
  apply typing.fvar; repeat simp
  apply typing_reification.reify
  apply typing.reflect; rw [← union_pure_left ∅]
  apply typing.binary₁
  apply typing.fvar; repeat simp
  apply typing.fvar; repeat simp

example : typing_reification [] [] expr₅ τ .reify :=
  by
  rw [expr₅, x₀, x₁, x₂, τ]
  apply typing_reification.reify
  apply typing.lam𝕔
  apply typing_reification.pure
  apply typing.let𝕔; rw [← union_pure_left ∅]
  apply typing.binary₁
  apply typing.fvar; repeat simp
  apply typing.fvar; repeat simp
  apply typing_reification.pure
  apply typing.let𝕔; rw [← union_pure_left ∅]
  apply typing.binary₁
  apply typing.fvar; repeat simp
  apply typing.fvar; repeat simp
  apply typing_reification.pure
  apply typing.code_rep
  apply typing.fvar; repeat simp

example : typing_reification [] [] expr₆ τ .reify :=
  by
  rw [expr₆, x₀, x₁, x₂, τ]
  apply typing_reification.reify
  apply typing.lam𝕔
  apply typing_reification.pure
  apply typing.let𝕔; rw [← union_pure_left ∅]
  apply typing.binary₁
  apply typing.fvar; repeat simp
  apply typing.fvar; repeat simp
  apply typing_reification.pure
  apply typing.code_rep; rw [← union_pure_left ∅]
  apply typing.lets; rw [← union_pure_left ∅]
  apply typing.binary₁
  apply typing.fvar; repeat simp
  apply typing.fvar; repeat simp
  apply typing.fvar; repeat simp

example : typing_reification [] [] expr₇ τ .reify :=
  by
  rw [expr₇, x₀, x₁, x₂, τ]
  apply typing_reification.reify
  apply typing.lam𝕔
  apply typing_reification.pure
  apply typing.code_rep; rw [← union_pure_left ∅]
  apply typing.lets; rw [← union_pure_left ∅]
  apply typing.binary₁
  apply typing.fvar; repeat simp
  apply typing.fvar; repeat simp
  rw [← union_pure_left .pure]
  apply typing.lets; rw [← union_pure_left ∅]
  apply typing.binary₁
  apply typing.fvar; repeat simp
  apply typing.fvar; repeat simp
  apply typing.fvar; repeat simp

example : typing_reification [] [] expr₈ τ .reify :=
  by
  rw [expr₈, x₀, x₁, x₂, τ]
  apply typing_reification.reify
  apply typing.reflect
  apply typing.lam; rw [← union_pure_left ∅]
  apply typing.lets; rw [← union_pure_left ∅]
  apply typing.binary₁
  apply typing.fvar; repeat simp
  apply typing.fvar; repeat simp
  rw [← union_pure_left .pure]
  apply typing.lets; rw [← union_pure_left ∅]
  apply typing.binary₁
  apply typing.fvar; repeat simp
  apply typing.fvar; repeat simp
  apply typing.fvar; repeat simp

example : typing_reification [] [] expr₉ τ .pure :=
  by
  rw [expr₉, x₀, x₁, x₂, τ]
  apply typing_reification.pure
  apply typing.let𝕔
  apply typing.lam
  apply typing.lets
  apply typing.binary₁
  apply typing.fvar; simp; rfl; simp
  apply typing.fvar; repeat simp
  apply typing.lets
  apply typing.binary₁
  apply typing.fvar; repeat simp
  apply typing.fvar; repeat simp
  apply typing.fvar; repeat simp
  repeat constructor

example : typing_reification [] [] expr𝕩 τ .pure :=
  by
  rw [expr𝕩, x₀, x₁, x₂, τ]
  apply typing_reification.pure
  apply typing.code_rep; rw [← union_pure_left ∅]
  apply typing.lets; rw [← union_pure_left ∅]
  apply typing.lam
  apply typing.lets
  apply typing.binary₁
  apply typing.fvar; simp; rfl; simp
  apply typing.fvar; repeat simp
  apply typing.lets
  apply typing.binary₁
  apply typing.fvar; repeat simp
  apply typing.fvar; repeat simp
  apply typing.fvar; repeat simp
  repeat constructor

end Fig4
