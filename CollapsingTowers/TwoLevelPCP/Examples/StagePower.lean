
import CollapsingTowers.TwoLevelPCP.Typing
namespace StagePower
-- stage power function xⁿ
-- let (power : <ℕ> → ℕ → <ℕ>) =
--   λ(x : <ℕ>).
--     fix₁ (
--       λ(f : ℕ → <ℕ>).
--       λ(n : ℕ).
--         ifz₁ n
--           then (lift 1)
--           else x *₂ f(n - 1)
--     ) in
-- lift (
--   λ(y : <ℕ>).
--     power(y)(2)
-- )
-- -->*
-- code (
--   let x₄ =
--     λ(x₀ : ℕ).
--       let x₁ = 1 in
--       let x₂ = x₀ * x₁ in
--       let x₃ = x₀ * x₂ in
--       x₃
--   in x₄
-- )
def x₀ : Expr :=
  .fvar 0

def x₁ : Expr :=
  .fvar 1

def x₂ : Expr :=
  .fvar 2

def x₃ : Expr :=
  .fvar 3

def x₄ : Expr :=
  .fvar 4

def power : Expr :=
  .fvar 100

def x : Expr :=
  .fvar 101

def f : Expr :=
  .fvar 102

def n : Expr :=
  .fvar 103

def y : Expr :=
  .fvar 104

def expr₀ : Expr :=
  .lets (
    .lam (close₀ 101 (
      .fix₁ (
        .lam (close₀ 102 (
        .lam (close₀ 103 (
          .ifz₁ n (
            .lift (.lit 1)) (
            .binary₂ .mul x (.app₁ f (.binary₁ .sub n (.lit 1)))))))))))) (close₀ 100 (
  .lift (
    .lam (close₀ 104 (
    .app₁ (.app₁ power y) (.lit 2))))))

def expr₁ : Expr :=
  .lift (
    .lam (close₀ 104 (
    .app₁ (
      .app₁ (
        .lam (close₀ 101 (
          .fix₁ (
            .lam (close₀ 102 (
            .lam (close₀ 103 (
              .ifz₁ n (
                .lift (.lit 1)) (
                .binary₂ .mul x (.app₁ f (.binary₁ .sub n (.lit 1))))))))))))
        y) (
      .lit 2))))

def expr₂ : Expr :=
  .lam𝕔 (close₀ 0 (
    .app₁ (
      .app₁ (
        .lam (close₀ 101 (
          .fix₁ (
            .lam (close₀ 102 (
            .lam (close₀ 103 (
              .ifz₁ n (
                .lift (.lit 1)) (
                .binary₂ .mul x (.app₁ f (.binary₁ .sub n (.lit 1))))))))))))
        (.code x₀)) (
      .lit 2)))

def expr₃ : Expr :=
  .lam𝕔 (close₀ 0 (
    .app₁ (
      .fix₁ (
        .lam (close₀ 102 (
        .lam (close₀ 103 (
          .ifz₁ n (
            .lift (.lit 1)) (
            .binary₂ .mul (.code x₀) (.app₁ f (.binary₁ .sub n (.lit 1)))))))))) (
      .lit 2)))

def expr₄ : Expr :=
  .lam𝕔 (close₀ 0 (
    .app₁ (
      .lam (close₀ 103 (
        .ifz₁ n (
          .lift (.lit 1)) (
          .binary₂ .mul (
            .code x₀) (
            .app₁ (
              .fix₁ (
                .lam (close₀ 102 (
                .lam (close₀ 103 (
                  .ifz₁ n (
                    .lift (.lit 1)) (
                    .binary₂ .mul (.code x₀) (.app₁ f (.binary₁ .sub n (.lit 1)))))))))) (
              .binary₁ .sub n (.lit 1))))))) (
      .lit 2)))

def expr₅ : Expr :=
  .lam𝕔 (close₀ 0 (
    .ifz₁ (.lit 2) (
      .lift (.lit 1)) (
      .binary₂ .mul (
        .code x₀) (
        .app₁ (
          .fix₁ (
            .lam (close₀ 102 (
            .lam (close₀ 103 (
              .ifz₁ n (
                .lift (.lit 1)) (
                .binary₂ .mul (.code x₀) (.app₁ f (.binary₁ .sub n (.lit 1)))))))))) (
          .binary₁ .sub (.lit 2) (.lit 1))))))

def expr₆ : Expr :=
  .lam𝕔 (close₀ 0 (
    .binary₂ .mul (
      .code x₀) (
      .app₁ (
        .fix₁ (
          .lam (close₀ 102 (
          .lam (close₀ 103 (
            .ifz₁ n (
              .lift (.lit 1)) (
              .binary₂ .mul (.code x₀) (.app₁ f (.binary₁ .sub n (.lit 1)))))))))) (
        .binary₁ .sub (.lit 2) (.lit 1)))))

def expr₇ : Expr :=
  .lam𝕔 (close₀ 0 (
    .binary₂ .mul (
      .code x₀) (
      .app₁ (
        .lam (close₀ 103 (
          .ifz₁ n (
            .lift (.lit 1)) (
            .binary₂ .mul (
              .code x₀) (
              .app₁ (
                .fix₁ (
                  .lam (close₀ 102 (
                  .lam (close₀ 103 (
                    .ifz₁ n (
                      .lift (.lit 1)) (
                      .binary₂ .mul (.code x₀) (.app₁ f (.binary₁ .sub n (.lit 1)))))))))) (
                .binary₁ .sub n (.lit 1))))))) (
        .binary₁ .sub (.lit 2) (.lit 1)))))

def expr₈ : Expr :=
  .lam𝕔 (close₀ 0 (
    .binary₂ .mul (
      .code x₀) (
      .app₁ (
        .lam (close₀ 103 (
          .ifz₁ n (
            .lift (.lit 1)) (
            .binary₂ .mul (
              .code x₀) (
              .app₁ (
                .fix₁ (
                  .lam (close₀ 102 (
                  .lam (close₀ 103 (
                    .ifz₁ n (
                      .lift (.lit 1)) (
                      .binary₂ .mul (.code x₀) (.app₁ f (.binary₁ .sub n (.lit 1)))))))))) (
                .binary₁ .sub n (.lit 1))))))) (
        .lit 1))))

def expr₉ : Expr :=
  .lam𝕔 (close₀ 0 (
    .binary₂ .mul (
      .code x₀) (
      .ifz₁ (.lit 1) (
        .lift (.lit 1)) (
        .binary₂ .mul (
          .code x₀) (
          .app₁ (
            .fix₁ (
              .lam (close₀ 102 (
              .lam (close₀ 103 (
                .ifz₁ n (
                  .lift (.lit 1)) (
                  .binary₂ .mul (.code x₀) (.app₁ f (.binary₁ .sub n (.lit 1)))))))))) (
            .binary₁ .sub (.lit 1) (.lit 1)))))))

def expr𝕩₀ : Expr :=
  .lam𝕔 (close₀ 0 (
    .binary₂ .mul (
      .code x₀) (
      .binary₂ .mul (
        .code x₀) (
        .app₁ (
          .fix₁ (
            .lam (close₀ 102 (
            .lam (close₀ 103 (
              .ifz₁ n (
                .lift (.lit 1)) (
                .binary₂ .mul (.code x₀) (.app₁ f (.binary₁ .sub n (.lit 1)))))))))) (
          .binary₁ .sub (.lit 1) (.lit 1))))))

def expr𝕩₁ : Expr :=
  .lam𝕔 (close₀ 0 (
    .binary₂ .mul (
      .code x₀) (
      .binary₂ .mul (
        .code x₀) (
        .app₁ (
          .lam (close₀ 103 (
            .ifz₁ n (
              .lift (.lit 1)) (
              .binary₂ .mul (
                .code x₀) (
                .app₁ (
                  .fix₁ (
                    .lam (close₀ 102 (
                    .lam (close₀ 103 (
                      .ifz₁ n (
                        .lift (.lit 1)) (
                        .binary₂ .mul (.code x₀) (.app₁ f (.binary₁ .sub n (.lit 1)))))))))) (
                  .binary₁ .sub n (.lit 1))))))) (
          .binary₁ .sub (.lit 1) (.lit 1))))))

def expr𝕩₂ : Expr :=
  .lam𝕔 (close₀ 0 (
    .binary₂ .mul (
      .code x₀) (
      .binary₂ .mul (
        .code x₀) (
        .app₁ (
          .lam (close₀ 103 (
            .ifz₁ n (
              .lift (.lit 1)) (
              .binary₂ .mul (
                .code x₀) (
                .app₁ (
                  .fix₁ (
                    .lam (close₀ 102 (
                    .lam (close₀ 103 (
                      .ifz₁ n (
                        .lift (.lit 1)) (
                        .binary₂ .mul (.code x₀) (.app₁ f (.binary₁ .sub n (.lit 1)))))))))) (
                  .binary₁ .sub n (.lit 1))))))) (
          .lit 0)))))

def expr𝕩₃ : Expr :=
  .lam𝕔 (close₀ 0 (
    .binary₂ .mul (
      .code x₀) (
      .binary₂ .mul (
        .code x₀) (
          .ifz₁ (.lit 0) (
            .lift (.lit 1)) (
            .binary₂ .mul (
              .code x₀) (
              .app₁ (
                .fix₁ (
                  .lam (close₀ 102 (
                  .lam (close₀ 103 (
                    .ifz₁ n (
                      .lift (.lit 1)) (
                      .binary₂ .mul (.code x₀) (.app₁ f (.binary₁ .sub n (.lit 1)))))))))) (
                .binary₁ .sub (.lit 0) (.lit 1))))))))

def expr𝕩₄ : Expr :=
  .lam𝕔 (close₀ 0 (
    .binary₂ .mul (
      .code x₀) (
      .binary₂ .mul (
        .code x₀) (
        .lift (.lit 1)))))

def expr𝕩₅ : Expr :=
  .lam𝕔 (close₀ 0 (
    .binary₂ .mul (
      .code x₀) (
      .binary₂ .mul (
        .code x₀) (
        .reflect (.lit 1)))))

def expr𝕩₆ : Expr :=
  .lam𝕔 (close₀ 0 (
    .let𝕔 (.lit 1) (close₀ 1 (
    .binary₂ .mul (
      .code x₀) (
      .binary₂ .mul (
        .code x₀) (
        .code x₁))))))

def expr𝕩₇ : Expr :=
  .lam𝕔 (close₀ 0 (
    .let𝕔 (.lit 1) (close₀ 1 (
    .binary₂ .mul (
      .code x₀) (
      .reflect (.binary₁ .mul x₀ x₁))))))

def expr𝕩₈ : Expr :=
  .lam𝕔 (close₀ 0 (
    .let𝕔 (.lit 1) (close₀ 1 (
    .let𝕔 (.binary₁ .mul x₀ x₁) (close₀ 2 (
    .binary₂ .mul (
      .code x₀) (
      .code x₂)))))))

def expr𝕩₉ : Expr :=
  .lam𝕔 (close₀ 0 (
    .let𝕔 (.lit 1) (close₀ 1 (
    .let𝕔 (.binary₁ .mul x₀ x₁) (close₀ 2 (
    .reflect (.binary₁ .mul x₀ x₂)))))))

def expr𝕩𝕩₀ : Expr :=
  .lam𝕔 (close₀ 0 (
    .let𝕔 (.lit 1) (close₀ 1 (
    .let𝕔 (.binary₁ .mul x₀ x₁) (close₀ 2 (
    .let𝕔 (.binary₁ .mul x₀ x₂) (close₀ 3 (
    .code x₃))))))))

def expr𝕩𝕩₁ : Expr :=
  .lam𝕔 (close₀ 0 (
    .let𝕔 (.lit 1) (close₀ 1 (
    .let𝕔 (.binary₁ .mul x₀ x₁) (close₀ 2 (
    .code (.lets (.binary₁ .mul x₀ x₂) (close₀ 3 x₃))))))))

def expr𝕩𝕩₂ : Expr :=
  .lam𝕔 (close₀ 0 (
    .let𝕔 (.lit 1) (close₀ 1 (
    .code (
      .lets (.binary₁ .mul x₀ x₁) (close₀ 2 (
      .lets (.binary₁ .mul x₀ x₂) (close₀ 3
      x₃))))))))

def expr𝕩𝕩₃ : Expr :=
  .lam𝕔 (close₀ 0 (
    .code (
      .lets (.lit 1) (close₀ 1 (
      .lets (.binary₁ .mul x₀ x₁) (close₀ 2 (
      .lets (.binary₁ .mul x₀ x₂) (close₀ 3
      x₃))))))))

def expr𝕩𝕩₄ : Expr :=
  .reflect (
    .lam (close₀ 0 (
      .lets (.lit 1) (close₀ 1 (
      .lets (.binary₁ .mul x₀ x₁) (close₀ 2 (
      .lets (.binary₁ .mul x₀ x₂) (close₀ 3
      x₃))))))))

def expr𝕩𝕩₅ : Expr :=
  .let𝕔 (
    .lam (close₀ 0 (
      .lets (.lit 1) (close₀ 1 (
      .lets (.binary₁ .mul x₀ x₁) (close₀ 2 (
      .lets (.binary₁ .mul x₀ x₂) (close₀ 3
      x₃)))))))) (close₀ 4 (
  .code x₄))

def expr𝕩𝕩₆ : Expr :=
  .code (
    .lets (
      .lam (close₀ 0 (
        .lets (.lit 1) (close₀ 1 (
        .lets (.binary₁ .mul x₀ x₁) (close₀ 2 (
        .lets (.binary₁ .mul x₀ x₂) (close₀ 3
        x₃)))))))) (close₀ 4 (
    x₄)))

example : step ([], expr₀) ([], expr₁) := by
  apply step_lvl.step𝕄 id
  repeat constructor

example : step ([], expr₁) ([], expr₂) := by
  apply step_lvl.step𝕄 id
  repeat constructor

example : step ([], expr₂) ([], expr₃) := by
  apply step_lvl.step𝕄 (fun X => .lam𝕔 (close₀ 0 (.app₁ X _)))
  apply ctx𝕄.consℝ (fun X => .lam𝕔 (close₀ 0 X))
  apply ctxℝ.lam𝕔
  apply ctx𝕄.cons𝔹 (fun X => .app₁ X _)
  repeat constructor

example : step ([], expr₃) ([], expr₄) := by
  apply step_lvl.step𝕄 (fun X => .lam𝕔 (close₀ 0 (.app₁ X _)))
  apply ctx𝕄.consℝ (fun X => .lam𝕔 (close₀ 0 X))
  apply ctxℝ.lam𝕔
  apply ctx𝕄.cons𝔹 (fun X => .app₁ X _)
  repeat constructor

example : step ([], expr₄) ([], expr₅) := by
  apply step_lvl.step𝕄 (fun X => .lam𝕔 (close₀ 0 X))
  apply ctx𝕄.consℝ (fun X => .lam𝕔 (close₀ 0 X))
  repeat constructor

example : step ([], expr₅) ([], expr₆) := by
  apply step_lvl.step𝕄 (fun X => .lam𝕔 (close₀ 0 X))
  apply ctx𝕄.consℝ (fun X => .lam𝕔 (close₀ 0 X))
  repeat constructor

example : step ([], expr₆) ([], expr₇) := by
  apply step_lvl.step𝕄 (fun X => .lam𝕔 (close₀ 0 (.binary₂ .mul (.code x₀) (.app₁ X _))))
  apply ctx𝕄.consℝ (fun X => .lam𝕔 (close₀ 0 X))
  apply ctxℝ.lam𝕔
  apply ctx𝕄.cons𝔹 (fun X => .binary₂ .mul (.code x₀) X)
  repeat constructor
  apply ctx𝕄.cons𝔹 (fun X => .app₁ X _)
  repeat constructor

example : step ([], expr₇) ([], expr₈) := by
  let left : Expr :=
    .lam (close₀ 103 (
    .ifz₁ n (
      .lift (.lit 1)) (
      .binary₂ .mul (
        .code x₀) (
        .app₁ (
          .fix₁ (
            .lam (close₀ 102 (
            .lam (close₀ 103 (
              .ifz₁ n (
                .lift (.lit 1)) (
                .binary₂ .mul (.code x₀) (.app₁ f (.binary₁ .sub n (.lit 1)))))))))) (
          .binary₁ .sub n (.lit 1))))))
  apply step_lvl.step𝕄 (fun X => .lam𝕔 (close₀ 0 (.binary₂ .mul (.code x₀) (.app₁ left X))))
  apply ctx𝕄.consℝ (fun X => .lam𝕔 (close₀ 0 X))
  apply ctxℝ.lam𝕔
  apply ctx𝕄.cons𝔹 (fun X => .binary₂ .mul (.code x₀) X)
  repeat constructor

example : step ([], expr₈) ([], expr₉) := by
  apply step_lvl.step𝕄 (fun X => .lam𝕔 (close₀ 0 (.binary₂ .mul (.code x₀) X)))
  apply ctx𝕄.consℝ (fun X => .lam𝕔 (close₀ 0 X))
  repeat constructor

example : step ([], expr₉) ([], expr𝕩₀) := by
  apply step_lvl.step𝕄 (fun X => .lam𝕔 (close₀ 0 (.binary₂ .mul (.code x₀) X)))
  apply ctx𝕄.consℝ (fun X => .lam𝕔 (close₀ 0 X))
  repeat constructor

example : step ([], expr𝕩₀) ([], expr𝕩₁) := by
  apply step_lvl.step𝕄 (fun X => .lam𝕔 (close₀ 0 (.binary₂ .mul (.code x₀) (.binary₂ .mul (.code x₀) (.app₁ X _)))))
  apply ctx𝕄.consℝ (fun X => .lam𝕔 (close₀ 0 X))
  repeat constructor
  apply ctx𝕄.cons𝔹 (fun X => .app₁ X _)
  repeat constructor

example : step ([], expr𝕩₁) ([], expr𝕩₂) := by
  let left : Expr :=
    .lam (close₀ 103 (
    .ifz₁ n (
      .lift (.lit 1)) (
      .binary₂ .mul (
        .code x₀) (
        .app₁ (
          .fix₁ (
            .lam (close₀ 102 (
            .lam (close₀ 103 (
              .ifz₁ n (
                .lift (.lit 1)) (
                .binary₂ .mul (.code x₀) (.app₁ f (.binary₁ .sub n (.lit 1)))))))))) (
          .binary₁ .sub n (.lit 1))))))
  apply step_lvl.step𝕄 (fun X => .lam𝕔 (close₀ 0 (.binary₂ .mul (.code x₀) (.binary₂ .mul (.code x₀) (.app₁ left X)))))
  apply ctx𝕄.consℝ (fun X => .lam𝕔 (close₀ 0 X))
  repeat constructor

example : step ([], expr𝕩₂) ([], expr𝕩₃) := by
  apply step_lvl.step𝕄 (fun X => .lam𝕔 (close₀ 0 (.binary₂ .mul (.code x₀) (.binary₂ .mul (.code x₀) X))))
  apply ctx𝕄.consℝ (fun X => .lam𝕔 (close₀ 0 X))
  repeat constructor

example : step ([], expr𝕩₃) ([], expr𝕩₄) := by
  apply step_lvl.step𝕄 (fun X => .lam𝕔 (close₀ 0 (.binary₂ .mul (.code x₀) (.binary₂ .mul (.code x₀) X))))
  apply ctx𝕄.consℝ (fun X => .lam𝕔 (close₀ 0 X))
  repeat constructor

example : step ([], expr𝕩₄) ([], expr𝕩₅) := by
  apply step_lvl.step𝕄 (fun X => .lam𝕔 (close₀ 0 (.binary₂ .mul (.code x₀) (.binary₂ .mul (.code x₀) X))))
  apply ctx𝕄.consℝ (fun X => .lam𝕔 (close₀ 0 X))
  repeat constructor

example : step ([], expr𝕩₅) ([], expr𝕩₆) := by
  apply step_lvl.reflect
    (fun X => .lam𝕔 (close₀ 0 X))
    (fun X =>
      .binary₂ .mul (
        .code x₀) (
        .binary₂ .mul (
          .code x₀) (
          X)))
  repeat constructor

example : step ([], expr𝕩₆) ([], expr𝕩₇) := by
  apply step_lvl.step𝕄
    (fun X =>
      .lam𝕔 (close₀ 0 (
        .let𝕔 (.lit 1) (close₀ 1 (
          .binary₂ .mul (.code x₀) X)))))
  apply ctx𝕄.consℝ (fun X => .lam𝕔 (close₀ 0 X))
  apply ctxℝ.lam𝕔
  apply ctx𝕄.consℝ (fun X => .let𝕔 (.lit 1) (close₀ 1 X))
  repeat constructor

example : step ([], expr𝕩₇) ([], expr𝕩₈) := by
  apply step_lvl.reflect
    (fun X => .lam𝕔 (close₀ 0 (.let𝕔 (.lit 1) (close₀ 1 X))))
    (fun X => .binary₂ .mul (.code x₀) X)
  apply ctxℙ.consℚ (fun X => .lam𝕔 (close₀ 0 (.let𝕔 (.lit 1) (close₀ 1 X))))
  apply ctxℚ.consℝ (fun X => .lam𝕔 (close₀ 0 X))
  repeat constructor

example : step ([], expr𝕩₈) ([], expr𝕩₉) := by
  apply step_lvl.step𝕄
    (fun X =>
      .lam𝕔 (close₀ 0 (
        .let𝕔 (.lit 1) (close₀ 1 (
        .let𝕔 (.binary₁ .mul x₀ x₁) (close₀ 2 (
        X)))))))
  apply ctx𝕄.consℝ (fun X => .lam𝕔 (close₀ 0 X))
  apply ctxℝ.lam𝕔
  apply ctx𝕄.consℝ (fun X => .let𝕔 (.lit 1) (close₀ 1 X))
  apply ctxℝ.let𝕔; constructor
  apply ctx𝕄.consℝ (fun X => .let𝕔 (.binary₁ .mul x₀ x₁) (close₀ 2 X))
  repeat constructor

example : step ([], expr𝕩₉) ([], expr𝕩𝕩₀) := by
  apply step_lvl.reflect
    (fun X =>
      .lam𝕔 (close₀ 0 (
        .let𝕔 (.lit 1) (close₀ 1 (
        .let𝕔 (.binary₁ .mul x₀ x₁) (close₀ 2
        X))))))
    id
  apply ctxℙ.consℚ
    (fun X =>
      .lam𝕔 (close₀ 0 (
        .let𝕔 (.lit 1) (close₀ 1 (
        .let𝕔 (.binary₁ .mul x₀ x₁) (close₀ 2
        X))))))
  apply ctxℚ.consℝ (fun X => .lam𝕔 (close₀ 0 X))
  apply ctxℝ.lam𝕔
  apply ctxℚ.consℝ (fun X => .let𝕔 (.lit 1) (close₀ 1 X))
  repeat constructor

example : step ([], expr𝕩𝕩₀) ([], expr𝕩𝕩₁) := by
  apply step_lvl.step𝕄 (fun X =>
    .lam𝕔 (close₀ 0 (
      .let𝕔 (.lit 1) (close₀ 1 (
      .let𝕔 (.binary₁ .mul x₀ x₁) (close₀ 2 (
      X)))))))
  apply ctx𝕄.consℝ (fun X => .lam𝕔 (close₀ 0 X))
  apply ctxℝ.lam𝕔
  apply ctx𝕄.consℝ (fun X => .let𝕔 (.lit 1) (close₀ 1 X))
  apply ctxℝ.let𝕔; constructor
  apply ctx𝕄.consℝ (fun X => .let𝕔 (.binary₁ .mul x₀ x₁) (close₀ 2 X))
  repeat constructor

example : step ([], expr𝕩𝕩₁) ([], expr𝕩𝕩₂) := by
  apply step_lvl.step𝕄
    (fun X =>
      .lam𝕔 (close₀ 0 (
        .let𝕔 (.lit 1) (close₀ 1 (
        X)))))
  apply ctx𝕄.consℝ (fun X => .lam𝕔 (close₀ 0 X))
  apply ctxℝ.lam𝕔
  apply ctx𝕄.consℝ (fun X => .let𝕔 (.lit 1) (close₀ 1 X))
  repeat constructor

example : step ([], expr𝕩𝕩₂) ([], expr𝕩𝕩₃) := by
  apply step_lvl.step𝕄 (fun X => .lam𝕔 (close₀ 0 X))
  apply ctx𝕄.consℝ (fun X => .lam𝕔 (close₀ 0 X))
  repeat constructor

example : step ([], expr𝕩𝕩₃) ([], expr𝕩𝕩₄) := by
  apply step_lvl.step𝕄 id
  repeat constructor

example : step ([], expr𝕩𝕩₄) ([], expr𝕩𝕩₅) := by
  apply step_lvl.reflect id id
  repeat constructor

example : step ([], expr𝕩𝕩₅) ([], expr𝕩𝕩₆) := by
  apply step_lvl.step𝕄 id
  repeat constructor

example : typing_reification [] [] expr₀ (.rep (.arrow .nat .nat ∅)) .reify :=
  by
  apply typing_reification.reify; rw [← union_pure_left .reify]
  apply typing.lets
  apply typing.lam
  apply typing.fix₁
  apply typing.lam
  apply typing.lam _ _ _ _ _ _ .reify; rw [← union_pure_left .reify]
  apply typing.ifz₁
  . repeat constructor
  . apply typing.lift_lit; apply typing.lit
  . repeat constructor
  repeat constructor

example : typing_reification [] [] expr𝕩𝕩₆ (.rep (.arrow .nat .nat ∅)) ∅ :=
  by
  repeat
    first
    | constructor
    | rw [← union_pure_left ∅]
end StagePower

namespace StageMutablePower
-- stage mutable power function xⁿ
-- let ref = alloc₂ (lift 1) in
-- let (power : <ℕ> → ℕ → <ℕ>) =
--   λ(x : <ℕ>).
--     fix₁ (
--       λ(f : ℕ → <ℕ>).
--       λ(n : ℕ).
--         ifz₁ n
--           then load₂ ref
--           else
--            let _ = store₂ ref (x *₂ (load₂ ref)) in
--            f(n - 1)
--     ) in
-- lift (
--   λ(y : <ℕ>).
--     power(y)(2)
-- )
-- -->*
-- code (
--   let x₀ = 1 in
--   let x₁ = alloc₁ x₀ in
--   let f₀ =
--     λ(x₂ : ℕ).
--       let x₃ = load₁ x₁ in
--       let x₄ = x₂ * x₃ in
--       let x₅ = store₁ x₁ x₄ in
--       let x₆ = load₁ x₁ in
--       let x₇ = x₂ * x₆ in
--       let x₈ = store₁ x₁ x₇ in
--       let x₉ = load₁ x₁ in
--       x₉
--   in f₀
-- )
def x₀ : Expr :=
  .fvar 0

def x₁ : Expr :=
  .fvar 1

def x₂ : Expr :=
  .fvar 2

def x₃ : Expr :=
  .fvar 3

def x₄ : Expr :=
  .fvar 4

def x₅ : Expr :=
  .fvar 5

def x₆ : Expr :=
  .fvar 6

def x₇ : Expr :=
  .fvar 7

def x₈ : Expr :=
  .fvar 8

def x₉ : Expr :=
  .fvar 9

def f₀ : Expr :=
  .fvar 10

def ref : Expr :=
  .fvar 100

def power : Expr :=
  .fvar 101

def x : Expr :=
  .fvar 102

def f : Expr :=
  .fvar 103

def n : Expr :=
  .fvar 104

def y : Expr :=
  .fvar 105

def expr₀ : Expr :=
  .lets (.alloc₂ (.lift (.lit 1))) (close₀ 100 (
  .lets (
    .lam (close₀ 102 (
      .fix₁ (
        .lam (close₀ 103 (
        .lam (close₀ 104 (
          .ifz₁ n (
            .load₂ ref) (
            .lets (.store₂ ref (.binary₂ .mul x (.load₂ ref))) (
            .app₁ f (.binary₁ .sub n (.lit 1)))))))))))) (close₀ 101 (
  .lift (
    .lam (close₀ 105 (
      .app₁ (.app₁ power y) (.lit 2))))))))

def expr₁ : Expr :=
  .lets (.alloc₂ (.reflect (.lit 1))) (close₀ 100 (
  .lets (
    .lam (close₀ 102 (
      .fix₁ (
        .lam (close₀ 103 (
        .lam (close₀ 104 (
          .ifz₁ n (
            .load₂ ref) (
            .lets (.store₂ ref (.binary₂ .mul x (.load₂ ref))) (
            .app₁ f (.binary₁ .sub n (.lit 1)))))))))))) (close₀ 101 (
  .lift (
    .lam (close₀ 105 (
      .app₁ (.app₁ power y) (.lit 2))))))))

def expr₂ : Expr :=
  .let𝕔 (.lit 1) (close₀ 0 (
  .lets (.alloc₂ (.code x₀)) (close₀ 100 (
  .lets (
    .lam (close₀ 102 (
      .fix₁ (
        .lam (close₀ 103 (
        .lam (close₀ 104 (
          .ifz₁ n (
            .load₂ ref) (
            .lets (.store₂ ref (.binary₂ .mul x (.load₂ ref))) (
            .app₁ f (.binary₁ .sub n (.lit 1)))))))))))) (close₀ 101 (
  .lift (
    .lam (close₀ 105 (
      .app₁ (.app₁ power y) (.lit 2))))))))))

def expr₃ : Expr :=
  .let𝕔 (.lit 1) (close₀ 0 (
  .lets (.reflect (.alloc₁ x₀)) (close₀ 100 (
  .lets (
    .lam (close₀ 102 (
      .fix₁ (
        .lam (close₀ 103 (
        .lam (close₀ 104 (
          .ifz₁ n (
            .load₂ ref) (
            .lets (.store₂ ref (.binary₂ .mul x (.load₂ ref))) (
            .app₁ f (.binary₁ .sub n (.lit 1)))))))))))) (close₀ 101 (
  .lift (
    .lam (close₀ 105 (
      .app₁ (.app₁ power y) (.lit 2))))))))))

def expr₄ : Expr :=
  .let𝕔 (.lit 1) (close₀ 0 (
  .let𝕔 (.alloc₁ x₀) (close₀ 1 (
  .lets (.code x₁) (close₀ 100 (
  .lets (
    .lam (close₀ 102 (
      .fix₁ (
        .lam (close₀ 103 (
        .lam (close₀ 104 (
          .ifz₁ n (
            .load₂ ref) (
            .lets (.store₂ ref (.binary₂ .mul x (.load₂ ref))) (
            .app₁ f (.binary₁ .sub n (.lit 1)))))))))))) (close₀ 101 (
  .lift (
    .lam (close₀ 105 (
      .app₁ (.app₁ power y) (.lit 2))))))))))))

def expr₅ : Expr :=
  .let𝕔 (.lit 1) (close₀ 0 (
  .let𝕔 (.alloc₁ x₀) (close₀ 1 (
  .lets (
    .lam (close₀ 102 (
      .fix₁ (
        .lam (close₀ 103 (
        .lam (close₀ 104 (
          .ifz₁ n (
            .load₂ (.code x₁)) (
            .lets (.store₂ (.code x₁) (.binary₂ .mul x (.load₂ (.code x₁)))) (
            .app₁ f (.binary₁ .sub n (.lit 1)))))))))))) (close₀ 101 (
  .lift (
    .lam (close₀ 105 (
      .app₁ (.app₁ power y) (.lit 2))))))))))

def expr₆ : Expr :=
  .let𝕔 (.lit 1) (close₀ 0 (
  .let𝕔 (.alloc₁ x₀) (close₀ 1 (
  .lift (
    .lam (close₀ 105 (
      .app₁ (
        .app₁ (
          .lam (close₀ 102 (
            .fix₁ (
              .lam (close₀ 103 (
              .lam (close₀ 104 (
                .ifz₁ n (
                  .load₂ (.code x₁)) (
                  .lets (.store₂ (.code x₁) (.binary₂ .mul x (.load₂ (.code x₁)))) (
                  .app₁ f (.binary₁ .sub n (.lit 1))))))))))))
          y) (
        .lit 2))))))))

def expr₇ : Expr :=
  .let𝕔 (.lit 1) (close₀ 0 (
  .let𝕔 (.alloc₁ x₀) (close₀ 1 (
    .lam𝕔 (close₀ 2 (
      .app₁ (
        .app₁ (
          .lam (close₀ 102 (
            .fix₁ (
              .lam (close₀ 103 (
              .lam (close₀ 104 (
                .ifz₁ n (
                  .load₂ (.code x₁)) (
                  .lets (.store₂ (.code x₁) (.binary₂ .mul x (.load₂ (.code x₁)))) (
                  .app₁ f (.binary₁ .sub n (.lit 1)))))))))))) (
          .code x₂)) (
        .lit 2)))))))

def expr₈ : Expr :=
  .let𝕔 (.lit 1) (close₀ 0 (
  .let𝕔 (.alloc₁ x₀) (close₀ 1 (
    .lam𝕔 (close₀ 2 (
      .app₁ (
        .fix₁ (
          .lam (close₀ 103 (
          .lam (close₀ 104 (
            .ifz₁ n (
              .load₂ (.code x₁)) (
              .lets (.store₂ (.code x₁) (.binary₂ .mul (.code x₂) (.load₂ (.code x₁)))) (
              .app₁ f (.binary₁ .sub n (.lit 1)))))))))) (
        .lit 2)))))))

def expr₉ : Expr :=
  .let𝕔 (.lit 1) (close₀ 0 (
  .let𝕔 (.alloc₁ x₀) (close₀ 1 (
    .lam𝕔 (close₀ 2 (
      .app₁ (
        .lam (close₀ 104 (
          .ifz₁ n (
            .load₂ (.code x₁)) (
            .lets (.store₂ (.code x₁) (.binary₂ .mul (.code x₂) (.load₂ (.code x₁)))) (
            .app₁ (
              .fix₁ (
                .lam (close₀ 103 (
                .lam (close₀ 104 (
                  .ifz₁ n (
                    .load₂ (.code x₁)) (
                    .lets (.store₂ (.code x₁) (.binary₂ .mul (.code x₂) (.load₂ (.code x₁)))) (
                    .app₁ f (.binary₁ .sub n (.lit 1)))))))))) (
              .binary₁ .sub n (.lit 1))))))) (
        .lit 2)))))))

def expr𝕩₀ : Expr :=
  .let𝕔 (.lit 1) (close₀ 0 (
  .let𝕔 (.alloc₁ x₀) (close₀ 1 (
    .lam𝕔 (close₀ 2 (
      .ifz₁ (.lit 2) (
        .load₂ (.code x₁)) (
        .lets (.store₂ (.code x₁) (.binary₂ .mul (.code x₂) (.load₂ (.code x₁)))) (
        .app₁ (
          .fix₁ (
            .lam (close₀ 103 (
            .lam (close₀ 104 (
              .ifz₁ n (
                .load₂ (.code x₁)) (
                .lets (.store₂ (.code x₁) (.binary₂ .mul (.code x₂) (.load₂ (.code x₁)))) (
                .app₁ f (.binary₁ .sub n (.lit 1)))))))))) (
          .binary₁ .sub (.lit 2) (.lit 1))))))))))

def expr𝕩₁ : Expr :=
  .let𝕔 (.lit 1) (close₀ 0 (
  .let𝕔 (.alloc₁ x₀) (close₀ 1 (
    .lam𝕔 (close₀ 2 (
      .lets (.store₂ (.code x₁) (.binary₂ .mul (.code x₂) (.load₂ (.code x₁)))) (
      .app₁ (
        .fix₁ (
          .lam (close₀ 103 (
          .lam (close₀ 104 (
            .ifz₁ n (
              .load₂ (.code x₁)) (
              .lets (.store₂ (.code x₁) (.binary₂ .mul (.code x₂) (.load₂ (.code x₁)))) (
              .app₁ f (.binary₁ .sub n (.lit 1)))))))))) (
        .binary₁ .sub (.lit 2) (.lit 1)))))))))

def expr𝕩₂ : Expr :=
  .let𝕔 (.lit 1) (close₀ 0 (
  .let𝕔 (.alloc₁ x₀) (close₀ 1 (
    .lam𝕔 (close₀ 2 (
      .lets (.store₂ (.code x₁) (.binary₂ .mul (.code x₂) (.reflect (.load₁ x₁)))) (
      .app₁ (
        .fix₁ (
          .lam (close₀ 103 (
          .lam (close₀ 104 (
            .ifz₁ n (
              .load₂ (.code x₁)) (
              .lets (.store₂ (.code x₁) (.binary₂ .mul (.code x₂) (.load₂ (.code x₁)))) (
              .app₁ f (.binary₁ .sub n (.lit 1)))))))))) (
        .binary₁ .sub (.lit 2) (.lit 1)))))))))

def expr𝕩₃ : Expr :=
  .let𝕔 (.lit 1) (close₀ 0 (
  .let𝕔 (.alloc₁ x₀) (close₀ 1 (
    .lam𝕔 (close₀ 2 (
      .let𝕔 (.load₁ x₁) (close₀ 3 (
      .lets (.store₂ (.code x₁) (.binary₂ .mul (.code x₂) (.code x₃))) (
      .app₁ (
        .fix₁ (
          .lam (close₀ 103 (
          .lam (close₀ 104 (
            .ifz₁ n (
              .load₂ (.code x₁)) (
              .lets (.store₂ (.code x₁) (.binary₂ .mul (.code x₂) (.load₂ (.code x₁)))) (
              .app₁ f (.binary₁ .sub n (.lit 1)))))))))) (
        .binary₁ .sub (.lit 2) (.lit 1)))))))))))

def expr𝕩₄ : Expr :=
  .let𝕔 (.lit 1) (close₀ 0 (
  .let𝕔 (.alloc₁ x₀) (close₀ 1 (
    .lam𝕔 (close₀ 2 (
      .let𝕔 (.load₁ x₁) (close₀ 3 (
      .lets (.store₂ (.code x₁) (.reflect (.binary₁ .mul x₂ x₃))) (
      .app₁ (
        .fix₁ (
          .lam (close₀ 103 (
          .lam (close₀ 104 (
            .ifz₁ n (
              .load₂ (.code x₁)) (
              .lets (.store₂ (.code x₁) (.binary₂ .mul (.code x₂) (.load₂ (.code x₁)))) (
              .app₁ f (.binary₁ .sub n (.lit 1)))))))))) (
        .binary₁ .sub (.lit 2) (.lit 1)))))))))))

def expr𝕩₅ : Expr :=
  .let𝕔 (.lit 1) (close₀ 0 (
  .let𝕔 (.alloc₁ x₀) (close₀ 1 (
    .lam𝕔 (close₀ 2 (
      .let𝕔 (.load₁ x₁) (close₀ 3 (
      .let𝕔 (.binary₁ .mul x₂ x₃) (close₀ 4 (
      .lets (.store₂ (.code x₁) (.code x₄)) (
      .app₁ (
        .fix₁ (
          .lam (close₀ 103 (
          .lam (close₀ 104 (
            .ifz₁ n (
              .load₂ (.code x₁)) (
              .lets (.store₂ (.code x₁) (.binary₂ .mul (.code x₂) (.load₂ (.code x₁)))) (
              .app₁ f (.binary₁ .sub n (.lit 1)))))))))) (
        .binary₁ .sub (.lit 2) (.lit 1)))))))))))))

def expr𝕩₆ : Expr :=
  .let𝕔 (.lit 1) (close₀ 0 (
  .let𝕔 (.alloc₁ x₀) (close₀ 1 (
    .lam𝕔 (close₀ 2 (
      .let𝕔 (.load₁ x₁) (close₀ 3 (
      .let𝕔 (.binary₁ .mul x₂ x₃) (close₀ 4 (
      .lets (.reflect (.store₁ x₁ x₄)) (
      .app₁ (
        .fix₁ (
          .lam (close₀ 103 (
          .lam (close₀ 104 (
            .ifz₁ n (
              .load₂ (.code x₁)) (
              .lets (.store₂ (.code x₁) (.binary₂ .mul (.code x₂) (.load₂ (.code x₁)))) (
              .app₁ f (.binary₁ .sub n (.lit 1)))))))))) (
        .binary₁ .sub (.lit 2) (.lit 1)))))))))))))

def expr𝕩₇ : Expr :=
  .let𝕔 (.lit 1) (close₀ 0 (
  .let𝕔 (.alloc₁ x₀) (close₀ 1 (
    .lam𝕔 (close₀ 2 (
      .let𝕔 (.load₁ x₁) (close₀ 3 (
      .let𝕔 (.binary₁ .mul x₂ x₃) (close₀ 4 (
      .let𝕔 (.store₁ x₁ x₄) (close₀ 5 (
      .lets (.code x₅) (
      .app₁ (
        .fix₁ (
          .lam (close₀ 103 (
          .lam (close₀ 104 (
            .ifz₁ n (
              .load₂ (.code x₁)) (
              .lets (.store₂ (.code x₁) (.binary₂ .mul (.code x₂) (.load₂ (.code x₁)))) (
              .app₁ f (.binary₁ .sub n (.lit 1)))))))))) (
        .binary₁ .sub (.lit 2) (.lit 1)))))))))))))))

def expr𝕩₈ : Expr :=
  .let𝕔 (.lit 1) (close₀ 0 (
  .let𝕔 (.alloc₁ x₀) (close₀ 1 (
    .lam𝕔 (close₀ 2 (
      .let𝕔 (.load₁ x₁) (close₀ 3 (
      .let𝕔 (.binary₁ .mul x₂ x₃) (close₀ 4 (
      .let𝕔 (.store₁ x₁ x₄) (close₀ 5 (
      .app₁ (
        .fix₁ (
          .lam (close₀ 103 (
          .lam (close₀ 104 (
            .ifz₁ n (
              .load₂ (.code x₁)) (
              .lets (.store₂ (.code x₁) (.binary₂ .mul (.code x₂) (.load₂ (.code x₁)))) (
              .app₁ f (.binary₁ .sub n (.lit 1)))))))))) (
        .binary₁ .sub (.lit 2) (.lit 1))))))))))))))

def expr𝕩₉ : Expr :=
  .let𝕔 (.lit 1) (close₀ 0 (
  .let𝕔 (.alloc₁ x₀) (close₀ 1 (
    .lam𝕔 (close₀ 2 (
      .let𝕔 (.load₁ x₁) (close₀ 3 (
      .let𝕔 (.binary₁ .mul x₂ x₃) (close₀ 4 (
      .let𝕔 (.store₁ x₁ x₄) (close₀ 5 (
      .app₁ (
        .lam (close₀ 104 (
          .ifz₁ n (
            .load₂ (.code x₁)) (
            .lets (.store₂ (.code x₁) (.binary₂ .mul (.code x₂) (.load₂ (.code x₁)))) (
            .app₁ (
              .fix₁ (
                .lam (close₀ 103 (
                .lam (close₀ 104 (
                  .ifz₁ n (
                    .load₂ (.code x₁)) (
                    .lets (.store₂ (.code x₁) (.binary₂ .mul (.code x₂) (.load₂ (.code x₁)))) (
                    .app₁ f (.binary₁ .sub n (.lit 1)))))))))) (
              .binary₁ .sub n (.lit 1))))))) (
        .binary₁ .sub (.lit 2) (.lit 1))))))))))))))

def expr𝕩𝕩₀ : Expr :=
  .let𝕔 (.lit 1) (close₀ 0 (
  .let𝕔 (.alloc₁ x₀) (close₀ 1 (
    .lam𝕔 (close₀ 2 (
      .let𝕔 (.load₁ x₁) (close₀ 3 (
      .let𝕔 (.binary₁ .mul x₂ x₃) (close₀ 4 (
      .let𝕔 (.store₁ x₁ x₄) (close₀ 5 (
      .app₁ (
        .lam (close₀ 104 (
          .ifz₁ n (
            .load₂ (.code x₁)) (
            .lets (.store₂ (.code x₁) (.binary₂ .mul (.code x₂) (.load₂ (.code x₁)))) (
            .app₁ (
              .fix₁ (
                .lam (close₀ 103 (
                .lam (close₀ 104 (
                  .ifz₁ n (
                    .load₂ (.code x₁)) (
                    .lets (.store₂ (.code x₁) (.binary₂ .mul (.code x₂) (.load₂ (.code x₁)))) (
                    .app₁ f (.binary₁ .sub n (.lit 1)))))))))) (
              .binary₁ .sub n (.lit 1))))))) (
        .lit 1)))))))))))))

def expr𝕩𝕩₁ : Expr :=
  .let𝕔 (.lit 1) (close₀ 0 (
  .let𝕔 (.alloc₁ x₀) (close₀ 1 (
    .lam𝕔 (close₀ 2 (
      .let𝕔 (.load₁ x₁) (close₀ 3 (
      .let𝕔 (.binary₁ .mul x₂ x₃) (close₀ 4 (
      .let𝕔 (.store₁ x₁ x₄) (close₀ 5 (
        .ifz₁ (.lit 1) (
          .load₂ (.code x₁)) (
          .lets (.store₂ (.code x₁) (.binary₂ .mul (.code x₂) (.load₂ (.code x₁)))) (
          .app₁ (
            .fix₁ (
              .lam (close₀ 103 (
              .lam (close₀ 104 (
                .ifz₁ n (
                  .load₂ (.code x₁)) (
                  .lets (.store₂ (.code x₁) (.binary₂ .mul (.code x₂) (.load₂ (.code x₁)))) (
                  .app₁ f (.binary₁ .sub n (.lit 1)))))))))) (
            .binary₁ .sub (.lit 1) (.lit 1))))))))))))))))

def expr𝕩𝕩₂ : Expr :=
  .let𝕔 (.lit 1) (close₀ 0 (
  .let𝕔 (.alloc₁ x₀) (close₀ 1 (
    .lam𝕔 (close₀ 2 (
      .let𝕔 (.load₁ x₁) (close₀ 3 (
      .let𝕔 (.binary₁ .mul x₂ x₃) (close₀ 4 (
      .let𝕔 (.store₁ x₁ x₄) (close₀ 5 (
      .lets (.store₂ (.code x₁) (.binary₂ .mul (.code x₂) (.load₂ (.code x₁)))) (
      .app₁ (
        .fix₁ (
          .lam (close₀ 103 (
          .lam (close₀ 104 (
            .ifz₁ n (
              .load₂ (.code x₁)) (
              .lets (.store₂ (.code x₁) (.binary₂ .mul (.code x₂) (.load₂ (.code x₁)))) (
              .app₁ f (.binary₁ .sub n (.lit 1)))))))))) (
        .binary₁ .sub (.lit 1) (.lit 1)))))))))))))))

def expr𝕩𝕩₃ : Expr :=
  .let𝕔 (.lit 1) (close₀ 0 (
  .let𝕔 (.alloc₁ x₀) (close₀ 1 (
    .lam𝕔 (close₀ 2 (
      .let𝕔 (.load₁ x₁) (close₀ 3 (
      .let𝕔 (.binary₁ .mul x₂ x₃) (close₀ 4 (
      .let𝕔 (.store₁ x₁ x₄) (close₀ 5 (
      .lets (.store₂ (.code x₁) (.binary₂ .mul (.code x₂) (.reflect (.load₁ x₁)))) (
      .app₁ (
        .fix₁ (
          .lam (close₀ 103 (
          .lam (close₀ 104 (
            .ifz₁ n (
              .load₂ (.code x₁)) (
              .lets (.store₂ (.code x₁) (.binary₂ .mul (.code x₂) (.load₂ (.code x₁)))) (
              .app₁ f (.binary₁ .sub n (.lit 1)))))))))) (
        .binary₁ .sub (.lit 1) (.lit 1)))))))))))))))

def expr𝕩𝕩₄ : Expr :=
  .let𝕔 (.lit 1) (close₀ 0 (
  .let𝕔 (.alloc₁ x₀) (close₀ 1 (
    .lam𝕔 (close₀ 2 (
      .let𝕔 (.load₁ x₁) (close₀ 3 (
      .let𝕔 (.binary₁ .mul x₂ x₃) (close₀ 4 (
      .let𝕔 (.store₁ x₁ x₄) (close₀ 5 (
      .let𝕔 (.load₁ x₁) (close₀ 6 (
      .lets (.store₂ (.code x₁) (.binary₂ .mul (.code x₂) (.code x₆))) (
      .app₁ (
        .fix₁ (
          .lam (close₀ 103 (
          .lam (close₀ 104 (
            .ifz₁ n (
              .load₂ (.code x₁)) (
              .lets (.store₂ (.code x₁) (.binary₂ .mul (.code x₂) (.load₂ (.code x₁)))) (
              .app₁ f (.binary₁ .sub n (.lit 1)))))))))) (
        .binary₁ .sub (.lit 1) (.lit 1)))))))))))))))))

def expr𝕩𝕩₅ : Expr :=
  .let𝕔 (.lit 1) (close₀ 0 (
  .let𝕔 (.alloc₁ x₀) (close₀ 1 (
    .lam𝕔 (close₀ 2 (
      .let𝕔 (.load₁ x₁) (close₀ 3 (
      .let𝕔 (.binary₁ .mul x₂ x₃) (close₀ 4 (
      .let𝕔 (.store₁ x₁ x₄) (close₀ 5 (
      .let𝕔 (.load₁ x₁) (close₀ 6 (
      .lets (.store₂ (.code x₁) (.reflect (.binary₁ .mul x₂ x₆))) (
      .app₁ (
        .fix₁ (
          .lam (close₀ 103 (
          .lam (close₀ 104 (
            .ifz₁ n (
              .load₂ (.code x₁)) (
              .lets (.store₂ (.code x₁) (.binary₂ .mul (.code x₂) (.load₂ (.code x₁)))) (
              .app₁ f (.binary₁ .sub n (.lit 1)))))))))) (
        .binary₁ .sub (.lit 1) (.lit 1)))))))))))))))))

def expr𝕩𝕩₆ : Expr :=
  .let𝕔 (.lit 1) (close₀ 0 (
  .let𝕔 (.alloc₁ x₀) (close₀ 1 (
    .lam𝕔 (close₀ 2 (
      .let𝕔 (.load₁ x₁) (close₀ 3 (
      .let𝕔 (.binary₁ .mul x₂ x₃) (close₀ 4 (
      .let𝕔 (.store₁ x₁ x₄) (close₀ 5 (
      .let𝕔 (.load₁ x₁) (close₀ 6 (
      .let𝕔 (.binary₁ .mul x₂ x₆) (close₀ 7 (
      .lets (.store₂ (.code x₁) (.code x₇)) (
      .app₁ (
        .fix₁ (
          .lam (close₀ 103 (
          .lam (close₀ 104 (
            .ifz₁ n (
              .load₂ (.code x₁)) (
              .lets (.store₂ (.code x₁) (.binary₂ .mul (.code x₂) (.load₂ (.code x₁)))) (
              .app₁ f (.binary₁ .sub n (.lit 1)))))))))) (
        .binary₁ .sub (.lit 1) (.lit 1)))))))))))))))))))

def expr𝕩𝕩₇ : Expr :=
  .let𝕔 (.lit 1) (close₀ 0 (
  .let𝕔 (.alloc₁ x₀) (close₀ 1 (
    .lam𝕔 (close₀ 2 (
      .let𝕔 (.load₁ x₁) (close₀ 3 (
      .let𝕔 (.binary₁ .mul x₂ x₃) (close₀ 4 (
      .let𝕔 (.store₁ x₁ x₄) (close₀ 5 (
      .let𝕔 (.load₁ x₁) (close₀ 6 (
      .let𝕔 (.binary₁ .mul x₂ x₆) (close₀ 7 (
      .lets (.reflect (.store₁ x₁ x₇)) (
      .app₁ (
        .fix₁ (
          .lam (close₀ 103 (
          .lam (close₀ 104 (
            .ifz₁ n (
              .load₂ (.code x₁)) (
              .lets (.store₂ (.code x₁) (.binary₂ .mul (.code x₂) (.load₂ (.code x₁)))) (
              .app₁ f (.binary₁ .sub n (.lit 1)))))))))) (
        .binary₁ .sub (.lit 1) (.lit 1)))))))))))))))))))

def expr𝕩𝕩₈ : Expr :=
  .let𝕔 (.lit 1) (close₀ 0 (
  .let𝕔 (.alloc₁ x₀) (close₀ 1 (
    .lam𝕔 (close₀ 2 (
      .let𝕔 (.load₁ x₁) (close₀ 3 (
      .let𝕔 (.binary₁ .mul x₂ x₃) (close₀ 4 (
      .let𝕔 (.store₁ x₁ x₄) (close₀ 5 (
      .let𝕔 (.load₁ x₁) (close₀ 6 (
      .let𝕔 (.binary₁ .mul x₂ x₆) (close₀ 7 (
      .let𝕔 (.store₁ x₁ x₇) (close₀ 8 (
      .lets (.code x₈) (
      .app₁ (
        .fix₁ (
          .lam (close₀ 103 (
          .lam (close₀ 104 (
            .ifz₁ n (
              .load₂ (.code x₁)) (
              .lets (.store₂ (.code x₁) (.binary₂ .mul (.code x₂) (.load₂ (.code x₁)))) (
              .app₁ f (.binary₁ .sub n (.lit 1)))))))))) (
        .binary₁ .sub (.lit 1) (.lit 1)))))))))))))))))))))

def expr𝕩𝕩₉ : Expr :=
  .let𝕔 (.lit 1) (close₀ 0 (
  .let𝕔 (.alloc₁ x₀) (close₀ 1 (
    .lam𝕔 (close₀ 2 (
      .let𝕔 (.load₁ x₁) (close₀ 3 (
      .let𝕔 (.binary₁ .mul x₂ x₃) (close₀ 4 (
      .let𝕔 (.store₁ x₁ x₄) (close₀ 5 (
      .let𝕔 (.load₁ x₁) (close₀ 6 (
      .let𝕔 (.binary₁ .mul x₂ x₆) (close₀ 7 (
      .let𝕔 (.store₁ x₁ x₇) (close₀ 8 (
      .app₁ (
        .fix₁ (
          .lam (close₀ 103 (
          .lam (close₀ 104 (
            .ifz₁ n (
              .load₂ (.code x₁)) (
              .lets (.store₂ (.code x₁) (.binary₂ .mul (.code x₂) (.load₂ (.code x₁)))) (
              .app₁ f (.binary₁ .sub n (.lit 1)))))))))) (
        .binary₁ .sub (.lit 1) (.lit 1))))))))))))))))))))

def expr𝕩𝕩𝕩₀ : Expr :=
  .let𝕔 (.lit 1) (close₀ 0 (
  .let𝕔 (.alloc₁ x₀) (close₀ 1 (
    .lam𝕔 (close₀ 2 (
      .let𝕔 (.load₁ x₁) (close₀ 3 (
      .let𝕔 (.binary₁ .mul x₂ x₃) (close₀ 4 (
      .let𝕔 (.store₁ x₁ x₄) (close₀ 5 (
      .let𝕔 (.load₁ x₁) (close₀ 6 (
      .let𝕔 (.binary₁ .mul x₂ x₆) (close₀ 7 (
      .let𝕔 (.store₁ x₁ x₇) (close₀ 8 (
      .app₁ (
        .lam (close₀ 104 (
          .ifz₁ n (
            .load₂ (.code x₁)) (
            .lets (.store₂ (.code x₁) (.binary₂ .mul (.code x₂) (.load₂ (.code x₁)))) (
            .app₁ (
              .fix₁ (
                .lam (close₀ 103 (
                .lam (close₀ 104 (
                  .ifz₁ n (
                    .load₂ (.code x₁)) (
                    .lets (.store₂ (.code x₁) (.binary₂ .mul (.code x₂) (.load₂ (.code x₁)))) (
                    .app₁ f (.binary₁ .sub n (.lit 1)))))))))) (
              .binary₁ .sub n (.lit 1))))))) (
        .binary₁ .sub (.lit 1) (.lit 1))))))))))))))))))))

def expr𝕩𝕩𝕩₁ : Expr :=
  .let𝕔 (.lit 1) (close₀ 0 (
  .let𝕔 (.alloc₁ x₀) (close₀ 1 (
    .lam𝕔 (close₀ 2 (
      .let𝕔 (.load₁ x₁) (close₀ 3 (
      .let𝕔 (.binary₁ .mul x₂ x₃) (close₀ 4 (
      .let𝕔 (.store₁ x₁ x₄) (close₀ 5 (
      .let𝕔 (.load₁ x₁) (close₀ 6 (
      .let𝕔 (.binary₁ .mul x₂ x₆) (close₀ 7 (
      .let𝕔 (.store₁ x₁ x₇) (close₀ 8 (
      .app₁ (
        .lam (close₀ 104 (
          .ifz₁ n (
            .load₂ (.code x₁)) (
            .lets (.store₂ (.code x₁) (.binary₂ .mul (.code x₂) (.load₂ (.code x₁)))) (
            .app₁ (
              .fix₁ (
                .lam (close₀ 103 (
                .lam (close₀ 104 (
                  .ifz₁ n (
                    .load₂ (.code x₁)) (
                    .lets (.store₂ (.code x₁) (.binary₂ .mul (.code x₂) (.load₂ (.code x₁)))) (
                    .app₁ f (.binary₁ .sub n (.lit 1)))))))))) (
              .binary₁ .sub n (.lit 1))))))) (
        .lit 0)))))))))))))))))))

def expr𝕩𝕩𝕩₂ : Expr :=
  .let𝕔 (.lit 1) (close₀ 0 (
  .let𝕔 (.alloc₁ x₀) (close₀ 1 (
    .lam𝕔 (close₀ 2 (
      .let𝕔 (.load₁ x₁) (close₀ 3 (
      .let𝕔 (.binary₁ .mul x₂ x₃) (close₀ 4 (
      .let𝕔 (.store₁ x₁ x₄) (close₀ 5 (
      .let𝕔 (.load₁ x₁) (close₀ 6 (
      .let𝕔 (.binary₁ .mul x₂ x₆) (close₀ 7 (
      .let𝕔 (.store₁ x₁ x₇) (close₀ 8 (
      .ifz₁ (.lit 0) (
        .load₂ (.code x₁)) (
        .lets (.store₂ (.code x₁) (.binary₂ .mul (.code x₂) (.load₂ (.code x₁)))) (
        .app₁ (
          .fix₁ (
            .lam (close₀ 103 (
            .lam (close₀ 104 (
              .ifz₁ n (
                .load₂ (.code x₁)) (
                .lets (.store₂ (.code x₁) (.binary₂ .mul (.code x₂) (.load₂ (.code x₁)))) (
                .app₁ f (.binary₁ .sub n (.lit 1)))))))))) (
          .binary₁ .sub (.lit 0) (.lit 1))))))))))))))))))))))

def expr𝕩𝕩𝕩₃ : Expr :=
  .let𝕔 (.lit 1) (close₀ 0 (
  .let𝕔 (.alloc₁ x₀) (close₀ 1 (
    .lam𝕔 (close₀ 2 (
      .let𝕔 (.load₁ x₁) (close₀ 3 (
      .let𝕔 (.binary₁ .mul x₂ x₃) (close₀ 4 (
      .let𝕔 (.store₁ x₁ x₄) (close₀ 5 (
      .let𝕔 (.load₁ x₁) (close₀ 6 (
      .let𝕔 (.binary₁ .mul x₂ x₆) (close₀ 7 (
      .let𝕔 (.store₁ x₁ x₇) (close₀ 8 (
      .load₂ (.code x₁)))))))))))))))))))

def expr𝕩𝕩𝕩₄ : Expr :=
  .let𝕔 (.lit 1) (close₀ 0 (
  .let𝕔 (.alloc₁ x₀) (close₀ 1 (
    .lam𝕔 (close₀ 2 (
      .let𝕔 (.load₁ x₁) (close₀ 3 (
      .let𝕔 (.binary₁ .mul x₂ x₃) (close₀ 4 (
      .let𝕔 (.store₁ x₁ x₄) (close₀ 5 (
      .let𝕔 (.load₁ x₁) (close₀ 6 (
      .let𝕔 (.binary₁ .mul x₂ x₆) (close₀ 7 (
      .let𝕔 (.store₁ x₁ x₇) (close₀ 8 (
      .reflect (.load₁ x₁)))))))))))))))))))

def expr𝕩𝕩𝕩₅ : Expr :=
  .let𝕔 (.lit 1) (close₀ 0 (
  .let𝕔 (.alloc₁ x₀) (close₀ 1 (
    .lam𝕔 (close₀ 2 (
      .let𝕔 (.load₁ x₁) (close₀ 3 (
      .let𝕔 (.binary₁ .mul x₂ x₃) (close₀ 4 (
      .let𝕔 (.store₁ x₁ x₄) (close₀ 5 (
      .let𝕔 (.load₁ x₁) (close₀ 6 (
      .let𝕔 (.binary₁ .mul x₂ x₆) (close₀ 7 (
      .let𝕔 (.store₁ x₁ x₇) (close₀ 8 (
      .let𝕔 (.load₁ x₁) (close₀ 9 (
      .code x₉))))))))))))))))))))

def expr𝕩𝕩𝕩₆ : Expr :=
  .let𝕔 (.lit 1) (close₀ 0 (
  .let𝕔 (.alloc₁ x₀) (close₀ 1 (
    .lam𝕔 (close₀ 2 (
      .let𝕔 (.load₁ x₁) (close₀ 3 (
      .let𝕔 (.binary₁ .mul x₂ x₃) (close₀ 4 (
      .let𝕔 (.store₁ x₁ x₄) (close₀ 5 (
      .let𝕔 (.load₁ x₁) (close₀ 6 (
      .let𝕔 (.binary₁ .mul x₂ x₆) (close₀ 7 (
      .let𝕔 (.store₁ x₁ x₇) (close₀ 8 (
      .code (
        .lets (.load₁ x₁) (close₀ 9 (
        x₉)))))))))))))))))))))

def expr𝕩𝕩𝕩₇ : Expr :=
  .let𝕔 (.lit 1) (close₀ 0 (
  .let𝕔 (.alloc₁ x₀) (close₀ 1 (
    .lam𝕔 (close₀ 2 (
      .let𝕔 (.load₁ x₁) (close₀ 3 (
      .let𝕔 (.binary₁ .mul x₂ x₃) (close₀ 4 (
      .let𝕔 (.store₁ x₁ x₄) (close₀ 5 (
      .let𝕔 (.load₁ x₁) (close₀ 6 (
      .let𝕔 (.binary₁ .mul x₂ x₆) (close₀ 7 (
      .code (
        .lets (.store₁ x₁ x₇) (close₀ 8 (
        .lets (.load₁ x₁) (close₀ 9 (
        x₉)))))))))))))))))))))

def expr𝕩𝕩𝕩₈ : Expr :=
  .let𝕔 (.lit 1) (close₀ 0 (
  .let𝕔 (.alloc₁ x₀) (close₀ 1 (
    .lam𝕔 (close₀ 2 (
      .let𝕔 (.load₁ x₁) (close₀ 3 (
      .let𝕔 (.binary₁ .mul x₂ x₃) (close₀ 4 (
      .let𝕔 (.store₁ x₁ x₄) (close₀ 5 (
      .let𝕔 (.load₁ x₁) (close₀ 6 (
      .code (
        .lets (.binary₁ .mul x₂ x₆) (close₀ 7 (
        .lets (.store₁ x₁ x₇) (close₀ 8 (
        .lets (.load₁ x₁) (close₀ 9 (
        x₉)))))))))))))))))))))

def expr𝕩𝕩𝕩₉ : Expr :=
  .let𝕔 (.lit 1) (close₀ 0 (
  .let𝕔 (.alloc₁ x₀) (close₀ 1 (
    .lam𝕔 (close₀ 2 (
      .let𝕔 (.load₁ x₁) (close₀ 3 (
      .let𝕔 (.binary₁ .mul x₂ x₃) (close₀ 4 (
      .let𝕔 (.store₁ x₁ x₄) (close₀ 5 (
      .code (
        .lets (.load₁ x₁) (close₀ 6 (
        .lets (.binary₁ .mul x₂ x₆) (close₀ 7 (
        .lets (.store₁ x₁ x₇) (close₀ 8 (
        .lets (.load₁ x₁) (close₀ 9 (
        x₉)))))))))))))))))))))

def expr𝕩𝕩𝕩𝕩₀ : Expr :=
  .let𝕔 (.lit 1) (close₀ 0 (
  .let𝕔 (.alloc₁ x₀) (close₀ 1 (
    .lam𝕔 (close₀ 2 (
      .let𝕔 (.load₁ x₁) (close₀ 3 (
      .let𝕔 (.binary₁ .mul x₂ x₃) (close₀ 4 (
      .code (
        .lets (.store₁ x₁ x₄) (close₀ 5 (
        .lets (.load₁ x₁) (close₀ 6 (
        .lets (.binary₁ .mul x₂ x₆) (close₀ 7 (
        .lets (.store₁ x₁ x₇) (close₀ 8 (
        .lets (.load₁ x₁) (close₀ 9 (
        x₉)))))))))))))))))))))

def expr𝕩𝕩𝕩𝕩₁ : Expr :=
  .let𝕔 (.lit 1) (close₀ 0 (
  .let𝕔 (.alloc₁ x₀) (close₀ 1 (
    .lam𝕔 (close₀ 2 (
      .let𝕔 (.load₁ x₁) (close₀ 3 (
      .code (
        .lets (.binary₁ .mul x₂ x₃) (close₀ 4 (
        .lets (.store₁ x₁ x₄) (close₀ 5 (
        .lets (.load₁ x₁) (close₀ 6 (
        .lets (.binary₁ .mul x₂ x₆) (close₀ 7 (
        .lets (.store₁ x₁ x₇) (close₀ 8 (
        .lets (.load₁ x₁) (close₀ 9 (
        x₉)))))))))))))))))))))

def expr𝕩𝕩𝕩𝕩₂ : Expr :=
  .let𝕔 (.lit 1) (close₀ 0 (
  .let𝕔 (.alloc₁ x₀) (close₀ 1 (
    .lam𝕔 (close₀ 2 (
      .code (
        .lets (.load₁ x₁) (close₀ 3 (
        .lets (.binary₁ .mul x₂ x₃) (close₀ 4 (
        .lets (.store₁ x₁ x₄) (close₀ 5 (
        .lets (.load₁ x₁) (close₀ 6 (
        .lets (.binary₁ .mul x₂ x₆) (close₀ 7 (
        .lets (.store₁ x₁ x₇) (close₀ 8 (
        .lets (.load₁ x₁) (close₀ 9 (
        x₉)))))))))))))))))))))

def expr𝕩𝕩𝕩𝕩₃ : Expr :=
  .let𝕔 (.lit 1) (close₀ 0 (
  .let𝕔 (.alloc₁ x₀) (close₀ 1 (
    .reflect (
      .lam (close₀ 2 (
        .lets (.load₁ x₁) (close₀ 3 (
        .lets (.binary₁ .mul x₂ x₃) (close₀ 4 (
        .lets (.store₁ x₁ x₄) (close₀ 5 (
        .lets (.load₁ x₁) (close₀ 6 (
        .lets (.binary₁ .mul x₂ x₆) (close₀ 7 (
        .lets (.store₁ x₁ x₇) (close₀ 8 (
        .lets (.load₁ x₁) (close₀ 9 (
        x₉)))))))))))))))))))))

def expr𝕩𝕩𝕩𝕩₄ : Expr :=
  .let𝕔 (.lit 1) (close₀ 0 (
  .let𝕔 (.alloc₁ x₀) (close₀ 1 (
  .let𝕔 (
    .lam (close₀ 2 (
      .lets (.load₁ x₁) (close₀ 3 (
      .lets (.binary₁ .mul x₂ x₃) (close₀ 4 (
      .lets (.store₁ x₁ x₄) (close₀ 5 (
      .lets (.load₁ x₁) (close₀ 6 (
      .lets (.binary₁ .mul x₂ x₆) (close₀ 7 (
      .lets (.store₁ x₁ x₇) (close₀ 8 (
      .lets (.load₁ x₁) (close₀ 9 (
      x₉))))))))))))))))) (close₀ 10 (
  .code f₀))))))

def expr𝕩𝕩𝕩𝕩₅ : Expr :=
  .let𝕔 (.lit 1) (close₀ 0 (
  .let𝕔 (.alloc₁ x₀) (close₀ 1 (
  .code (
    .lets (
      .lam (close₀ 2 (
        .lets (.load₁ x₁) (close₀ 3 (
        .lets (.binary₁ .mul x₂ x₃) (close₀ 4 (
        .lets (.store₁ x₁ x₄) (close₀ 5 (
        .lets (.load₁ x₁) (close₀ 6 (
        .lets (.binary₁ .mul x₂ x₆) (close₀ 7 (
        .lets (.store₁ x₁ x₇) (close₀ 8 (
        .lets (.load₁ x₁) (close₀ 9 (
        x₉))))))))))))))))) (close₀ 10 (
    f₀)))))))

def expr𝕩𝕩𝕩𝕩₆ : Expr :=
  .let𝕔 (.lit 1) (close₀ 0 (
  .code (
    .lets (.alloc₁ x₀) (close₀ 1 (
    .lets (
      .lam (close₀ 2 (
        .lets (.load₁ x₁) (close₀ 3 (
        .lets (.binary₁ .mul x₂ x₃) (close₀ 4 (
        .lets (.store₁ x₁ x₄) (close₀ 5 (
        .lets (.load₁ x₁) (close₀ 6 (
        .lets (.binary₁ .mul x₂ x₆) (close₀ 7 (
        .lets (.store₁ x₁ x₇) (close₀ 8 (
        .lets (.load₁ x₁) (close₀ 9 (
        x₉))))))))))))))))) (close₀ 10 (
    f₀)))))))

def expr𝕩𝕩𝕩𝕩₇ : Expr :=
  .code (
    .lets (.lit 1) (close₀ 0 (
    .lets (.alloc₁ x₀) (close₀ 1 (
    .lets (
      .lam (close₀ 2 (
        .lets (.load₁ x₁) (close₀ 3 (
        .lets (.binary₁ .mul x₂ x₃) (close₀ 4 (
        .lets (.store₁ x₁ x₄) (close₀ 5 (
        .lets (.load₁ x₁) (close₀ 6 (
        .lets (.binary₁ .mul x₂ x₆) (close₀ 7 (
        .lets (.store₁ x₁ x₇) (close₀ 8 (
        .lets (.load₁ x₁) (close₀ 9 (
        x₉))))))))))))))))) (close₀ 10 (
    f₀)))))))

example : step ([], expr₀) ([], expr₁) := by
  apply step_lvl.step𝕄 (fun X => .lets (.alloc₂ X) _)
  apply ctx𝕄.cons𝔹 (fun X => .lets X _)
  repeat constructor

example : step ([], expr₁) ([], expr₂) := by
  apply step_lvl.reflect id (fun X => .lets (.alloc₂ X) _)
  apply ctxℙ.hole
  apply ctx𝔼.cons𝔹 (fun X => .lets X _)
  repeat constructor

example : step ([], expr₂) ([], expr₃) := by
  apply step_lvl.step𝕄
    (fun X =>
      .let𝕔 (.lit 1) (close₀ 0 (
      .lets X _)))
  apply ctx𝕄.consℝ (fun X => .let𝕔 (.lit 1) (close₀ 0 X))
  apply ctxℝ.let𝕔; constructor
  apply ctx𝕄.cons𝔹 (fun X => .lets X _)
  repeat constructor

example : step ([], expr₃) ([], expr₄) := by
  apply step_lvl.reflect (fun X => .let𝕔 (.lit 1) (close₀ 0 X)) (fun X => .lets X _)
  apply ctxℙ.consℚ
  apply ctxℚ.holeℝ
  apply ctxℝ.let𝕔; constructor
  apply ctx𝔼.cons𝔹 (fun X => .lets X _)
  repeat constructor

example : step ([], expr₄) ([], expr₅) := by
  apply step_lvl.step𝕄
    (fun X =>
      .let𝕔 (.lit 1) (close₀ 0 (
      .let𝕔 (.alloc₁ x₀) (close₀ 1
      X))))
  apply ctx𝕄.consℝ (fun X => .let𝕔 (.lit 1) (close₀ 0 X))
  apply ctxℝ.let𝕔; constructor
  apply ctx𝕄.consℝ (fun X => .let𝕔 (.alloc₁ x₀) (close₀ 1 X))
  repeat constructor

example : step ([], expr₅) ([], expr₆) := by
  apply step_lvl.step𝕄
    (fun X =>
      .let𝕔 (.lit 1) (close₀ 0 (
      .let𝕔 (.alloc₁ x₀) (close₀ 1
      X))))
  apply ctx𝕄.consℝ (fun X => .let𝕔 (.lit 1) (close₀ 0 X))
  apply ctxℝ.let𝕔; constructor
  apply ctx𝕄.consℝ (fun X => .let𝕔 (.alloc₁ x₀) (close₀ 1 X))
  repeat constructor

example : step ([], expr₆) ([], expr₇) := by
  apply step_lvl.step𝕄
    (fun X =>
      .let𝕔 (.lit 1) (close₀ 0 (
      .let𝕔 (.alloc₁ x₀) (close₀ 1
      X))))
  apply ctx𝕄.consℝ (fun X => .let𝕔 (.lit 1) (close₀ 0 X))
  apply ctxℝ.let𝕔; constructor
  apply ctx𝕄.consℝ (fun X => .let𝕔 (.alloc₁ x₀) (close₀ 1 X))
  repeat constructor

example : step ([], expr₇) ([], expr₈) := by
  apply step_lvl.step𝕄
    (fun X =>
      .let𝕔 (.lit 1) (close₀ 0 (
      .let𝕔 (.alloc₁ x₀) (close₀ 1 (
        .lam𝕔 (close₀ 2 (
          .app₁ X _)))))))
  apply ctx𝕄.consℝ (fun X => .let𝕔 (.lit 1) (close₀ 0 X))
  apply ctxℝ.let𝕔; constructor
  apply ctx𝕄.consℝ (fun X => .let𝕔 (.alloc₁ x₀) (close₀ 1 X))
  apply ctxℝ.let𝕔; constructor
  apply ctx𝕄.consℝ (fun X => .lam𝕔 (close₀ 2 X))
  apply ctxℝ.lam𝕔
  apply ctx𝕄.cons𝔹 (fun X => .app₁ X _)
  repeat constructor

example : step ([], expr₈) ([], expr₉) := by
  apply step_lvl.step𝕄
    (fun X =>
      .let𝕔 (.lit 1) (close₀ 0 (
      .let𝕔 (.alloc₁ x₀) (close₀ 1 (
        .lam𝕔 (close₀ 2 (
          .app₁ X _)))))))
  apply ctx𝕄.consℝ (fun X => .let𝕔 (.lit 1) (close₀ 0 X))
  apply ctxℝ.let𝕔; constructor
  apply ctx𝕄.consℝ (fun X => .let𝕔 (.alloc₁ x₀) (close₀ 1 X))
  apply ctxℝ.let𝕔; constructor
  apply ctx𝕄.consℝ (fun X => .lam𝕔 (close₀ 2 X))
  apply ctxℝ.lam𝕔
  apply ctx𝕄.cons𝔹 (fun X => .app₁ X _)
  repeat constructor

example : step ([], expr₉) ([], expr𝕩₀) := by
  apply step_lvl.step𝕄
    (fun X =>
      .let𝕔 (.lit 1) (close₀ 0 (
      .let𝕔 (.alloc₁ x₀) (close₀ 1 (
        .lam𝕔 (close₀ 2
          X))))))
  apply ctx𝕄.consℝ (fun X => .let𝕔 (.lit 1) (close₀ 0 X))
  apply ctxℝ.let𝕔; constructor
  apply ctx𝕄.consℝ (fun X => .let𝕔 (.alloc₁ x₀) (close₀ 1 X))
  apply ctxℝ.let𝕔; constructor
  apply ctx𝕄.consℝ (fun X => .lam𝕔 (close₀ 2 X))
  repeat constructor

example : step ([], expr𝕩₀) ([], expr𝕩₁) := by
  apply step_lvl.step𝕄
    (fun X =>
      .let𝕔 (.lit 1) (close₀ 0 (
      .let𝕔 (.alloc₁ x₀) (close₀ 1 (
        .lam𝕔 (close₀ 2
          X))))))
  apply ctx𝕄.consℝ (fun X => .let𝕔 (.lit 1) (close₀ 0 X))
  apply ctxℝ.let𝕔; constructor
  apply ctx𝕄.consℝ (fun X => .let𝕔 (.alloc₁ x₀) (close₀ 1 X))
  apply ctxℝ.let𝕔; constructor
  apply ctx𝕄.consℝ (fun X => .lam𝕔 (close₀ 2 X))
  repeat constructor

example : step ([], expr𝕩₁) ([], expr𝕩₂) := by
  apply step_lvl.step𝕄
    (fun X =>
      .let𝕔 (.lit 1) (close₀ 0 (
      .let𝕔 (.alloc₁ x₀) (close₀ 1 (
        .lam𝕔 (close₀ 2 (
          .lets (.store₂ (.code x₁) (.binary₂ .mul (.code x₂) X)) _)))))))
  apply ctx𝕄.consℝ (fun X => .let𝕔 (.lit 1) (close₀ 0 X))
  apply ctxℝ.let𝕔; constructor
  apply ctx𝕄.consℝ (fun X => .let𝕔 (.alloc₁ x₀) (close₀ 1 X))
  apply ctxℝ.let𝕔; constructor
  apply ctx𝕄.consℝ (fun X => .lam𝕔 (close₀ 2 X))
  apply ctxℝ.lam𝕔
  apply ctx𝕄.cons𝔹 (fun X => .lets X _)
  repeat constructor

example : step ([], expr𝕩₂) ([], expr𝕩₃) := by
  apply step_lvl.reflect
    (fun X =>
      .let𝕔 (.lit 1) (close₀ 0 (
      .let𝕔 (.alloc₁ x₀) (close₀ 1 (
        .lam𝕔 (close₀ 2 X))))))
    (fun X => .lets (.store₂ (.code x₁) (.binary₂ .mul (.code x₂) X)) _)
  apply ctxℙ.consℚ
  apply ctxℚ.consℝ (fun X => .let𝕔 (.lit 1) (close₀ 0 X))
  apply ctxℝ.let𝕔; constructor
  apply ctxℚ.consℝ (fun X => .let𝕔 (.alloc₁ x₀) (close₀ 1 X))
  apply ctxℝ.let𝕔; constructor
  apply ctxℚ.holeℝ (fun X => .lam𝕔 (close₀ 2 X))
  apply ctxℝ.lam𝕔
  apply ctx𝔼.cons𝔹 (fun X => .lets X _)
  repeat constructor

example : step ([], expr𝕩₃) ([], expr𝕩₄) := by
  apply step_lvl.step𝕄
    (fun X =>
      .let𝕔 (.lit 1) (close₀ 0 (
      .let𝕔 (.alloc₁ x₀) (close₀ 1 (
        .lam𝕔 (close₀ 2 (
          .let𝕔 (.load₁ x₁) (close₀ 3 (
          .lets (.store₂ (.code x₁) X) _)))))))))
  apply ctx𝕄.consℝ (fun X => .let𝕔 (.lit 1) (close₀ 0 X))
  apply ctxℝ.let𝕔; constructor
  apply ctx𝕄.consℝ (fun X => .let𝕔 (.alloc₁ x₀) (close₀ 1 X))
  apply ctxℝ.let𝕔; constructor
  apply ctx𝕄.consℝ (fun X => .lam𝕔 (close₀ 2 X))
  apply ctxℝ.lam𝕔
  apply ctx𝕄.consℝ (fun X => .let𝕔 (.load₁ x₁) (close₀ 3 X))
  apply ctxℝ.let𝕔; constructor
  apply ctx𝕄.cons𝔹 (fun X => .lets X _)
  repeat constructor

example : step ([], expr𝕩₄) ([], expr𝕩₅) := by
  apply step_lvl.reflect
    (fun X =>
      .let𝕔 (.lit 1) (close₀ 0 (
      .let𝕔 (.alloc₁ x₀) (close₀ 1 (
        .lam𝕔 (close₀ 2 (
          .let𝕔 (.load₁ x₁) (close₀ 3 X))))))))
    (fun X => .lets (.store₂ (.code x₁) X) _)
  apply ctxℙ.consℚ
  apply ctxℚ.consℝ (fun X => .let𝕔 (.lit 1) (close₀ 0 X))
  apply ctxℝ.let𝕔; constructor
  apply ctxℚ.consℝ (fun X => .let𝕔 (.alloc₁ x₀) (close₀ 1 X))
  apply ctxℝ.let𝕔; constructor
  apply ctxℚ.consℝ (fun X => .lam𝕔 (close₀ 2 X))
  apply ctxℝ.lam𝕔
  apply ctxℚ.holeℝ (fun X => .let𝕔 (.load₁ x₁) (close₀ 3 X))
  apply ctxℝ.let𝕔; constructor
  apply ctx𝔼.cons𝔹 (fun X => .lets X _)
  repeat constructor

example : step ([], expr𝕩₅) ([], expr𝕩₆) := by
  apply step_lvl.step𝕄
    (fun X =>
      .let𝕔 (.lit 1) (close₀ 0 (
      .let𝕔 (.alloc₁ x₀) (close₀ 1 (
        .lam𝕔 (close₀ 2 (
          .let𝕔 (.load₁ x₁) (close₀ 3 (
          .let𝕔 (.binary₁ .mul x₂ x₃) (close₀ 4 (
          .lets X _)))))))))))
  apply ctx𝕄.consℝ (fun X => .let𝕔 (.lit 1) (close₀ 0 X))
  apply ctxℝ.let𝕔; constructor
  apply ctx𝕄.consℝ (fun X => .let𝕔 (.alloc₁ x₀) (close₀ 1 X))
  apply ctxℝ.let𝕔; constructor
  apply ctx𝕄.consℝ (fun X => .lam𝕔 (close₀ 2 X))
  apply ctxℝ.lam𝕔
  apply ctx𝕄.consℝ (fun X => .let𝕔 (.load₁ x₁) (close₀ 3 X))
  apply ctxℝ.let𝕔; constructor
  apply ctx𝕄.consℝ (fun X => .let𝕔 (.binary₁ .mul x₂ x₃) (close₀ 4 X))
  apply ctxℝ.let𝕔; repeat constructor
  apply ctx𝕄.cons𝔹 (fun X => .lets X _)
  repeat constructor

example : step ([], expr𝕩₆) ([], expr𝕩₇) := by
  apply step_lvl.reflect
    (fun X =>
      .let𝕔 (.lit 1) (close₀ 0 (
      .let𝕔 (.alloc₁ x₀) (close₀ 1 (
        .lam𝕔 (close₀ 2 (
          .let𝕔 (.load₁ x₁) (close₀ 3 (
          .let𝕔 (.binary₁ .mul x₂ x₃) (close₀ 4 X))))))))))
    (fun X => .lets X _)
  apply ctxℙ.consℚ
  apply ctxℚ.consℝ (fun X => .let𝕔 (.lit 1) (close₀ 0 X))
  apply ctxℝ.let𝕔; constructor
  apply ctxℚ.consℝ (fun X => .let𝕔 (.alloc₁ x₀) (close₀ 1 X))
  apply ctxℝ.let𝕔; constructor
  apply ctxℚ.consℝ (fun X => .lam𝕔 (close₀ 2 X))
  apply ctxℝ.lam𝕔
  apply ctxℚ.consℝ (fun X => .let𝕔 (.load₁ x₁) (close₀ 3 X))
  apply ctxℝ.let𝕔; constructor
  apply ctxℚ.holeℝ (fun X => .let𝕔 (.binary₁ .mul x₂ x₃) (close₀ 4 X))
  apply ctxℝ.let𝕔; repeat constructor
  apply ctx𝔼.cons𝔹 (fun X => .lets X _)
  repeat constructor

example : step ([], expr𝕩₇) ([], expr𝕩₈) := by
  apply step_lvl.step𝕄
    (fun X =>
      .let𝕔 (.lit 1) (close₀ 0 (
      .let𝕔 (.alloc₁ x₀) (close₀ 1 (
        .lam𝕔 (close₀ 2 (
          .let𝕔 (.load₁ x₁) (close₀ 3 (
          .let𝕔 (.binary₁ .mul x₂ x₃) (close₀ 4 (
          .let𝕔 (.store₁ x₁ x₄) (close₀ 5 X))))))))))))
  apply ctx𝕄.consℝ (fun X => .let𝕔 (.lit 1) (close₀ 0 X))
  apply ctxℝ.let𝕔; constructor
  apply ctx𝕄.consℝ (fun X => .let𝕔 (.alloc₁ x₀) (close₀ 1 X))
  apply ctxℝ.let𝕔; constructor
  apply ctx𝕄.consℝ (fun X => .lam𝕔 (close₀ 2 X))
  apply ctxℝ.lam𝕔
  apply ctx𝕄.consℝ (fun X => .let𝕔 (.load₁ x₁) (close₀ 3 X))
  apply ctxℝ.let𝕔; constructor
  apply ctx𝕄.consℝ (fun X => .let𝕔 (.binary₁ .mul x₂ x₃) (close₀ 4 X))
  apply ctxℝ.let𝕔; constructor; constructor; constructor
  apply ctx𝕄.consℝ (fun X => .let𝕔 (.store₁ x₁ x₄) (close₀ 5 X))
  apply ctxℝ.let𝕔; repeat constructor

example : step ([], expr𝕩₈) ([], expr𝕩₉) := by
  apply step_lvl.step𝕄
    (fun X =>
      .let𝕔 (.lit 1) (close₀ 0 (
      .let𝕔 (.alloc₁ x₀) (close₀ 1 (
        .lam𝕔 (close₀ 2 (
          .let𝕔 (.load₁ x₁) (close₀ 3 (
          .let𝕔 (.binary₁ .mul x₂ x₃) (close₀ 4 (
          .let𝕔 (.store₁ x₁ x₄) (close₀ 5 (
          .app₁ X _)))))))))))))
  apply ctx𝕄.consℝ (fun X => .let𝕔 (.lit 1) (close₀ 0 X))
  apply ctxℝ.let𝕔; constructor
  apply ctx𝕄.consℝ (fun X => .let𝕔 (.alloc₁ x₀) (close₀ 1 X))
  apply ctxℝ.let𝕔; constructor
  apply ctx𝕄.consℝ (fun X => .lam𝕔 (close₀ 2 X))
  apply ctxℝ.lam𝕔
  apply ctx𝕄.consℝ (fun X => .let𝕔 (.load₁ x₁) (close₀ 3 X))
  apply ctxℝ.let𝕔; constructor
  apply ctx𝕄.consℝ (fun X => .let𝕔 (.binary₁ .mul x₂ x₃) (close₀ 4 X))
  apply ctxℝ.let𝕔; constructor; constructor; constructor
  apply ctx𝕄.consℝ (fun X => .let𝕔 (.store₁ x₁ x₄) (close₀ 5 X))
  apply ctxℝ.let𝕔; repeat constructor
  apply ctx𝕄.cons𝔹 (fun X => .app₁ X _)
  repeat constructor

example : step ([], expr𝕩₉) ([], expr𝕩𝕩₀) := by
  let left : Expr :=
    .lam (close₀ 104 (
      .ifz₁ n (
        .load₂ (.code x₁)) (
        .lets (.store₂ (.code x₁) (.binary₂ .mul (.code x₂) (.load₂ (.code x₁)))) (
        .app₁ (
          .fix₁ (
            .lam (close₀ 103 (
            .lam (close₀ 104 (
              .ifz₁ n (
                .load₂ (.code x₁)) (
                .lets (.store₂ (.code x₁) (.binary₂ .mul (.code x₂) (.load₂ (.code x₁)))) (
                .app₁ f (.binary₁ .sub n (.lit 1)))))))))) (
          .binary₁ .sub n (.lit 1))))))
  apply step_lvl.step𝕄
    (fun X =>
      .let𝕔 (.lit 1) (close₀ 0 (
      .let𝕔 (.alloc₁ x₀) (close₀ 1 (
        .lam𝕔 (close₀ 2 (
          .let𝕔 (.load₁ x₁) (close₀ 3 (
          .let𝕔 (.binary₁ .mul x₂ x₃) (close₀ 4 (
          .let𝕔 (.store₁ x₁ x₄) (close₀ 5 (
          .app₁ left X)))))))))))))
  apply ctx𝕄.consℝ (fun X => .let𝕔 (.lit 1) (close₀ 0 X))
  apply ctxℝ.let𝕔; constructor
  apply ctx𝕄.consℝ (fun X => .let𝕔 (.alloc₁ x₀) (close₀ 1 X))
  apply ctxℝ.let𝕔; constructor
  apply ctx𝕄.consℝ (fun X => .lam𝕔 (close₀ 2 X))
  apply ctxℝ.lam𝕔
  apply ctx𝕄.consℝ (fun X => .let𝕔 (.load₁ x₁) (close₀ 3 X))
  apply ctxℝ.let𝕔; constructor
  apply ctx𝕄.consℝ (fun X => .let𝕔 (.binary₁ .mul x₂ x₃) (close₀ 4 X))
  apply ctxℝ.let𝕔; constructor; constructor; constructor
  apply ctx𝕄.consℝ (fun X => .let𝕔 (.store₁ x₁ x₄) (close₀ 5 X))
  apply ctxℝ.let𝕔; repeat constructor

example : step ([], expr𝕩𝕩₀) ([], expr𝕩𝕩₁) := by
  apply step_lvl.step𝕄
    (fun X =>
      .let𝕔 (.lit 1) (close₀ 0 (
      .let𝕔 (.alloc₁ x₀) (close₀ 1 (
        .lam𝕔 (close₀ 2 (
          .let𝕔 (.load₁ x₁) (close₀ 3 (
          .let𝕔 (.binary₁ .mul x₂ x₃) (close₀ 4 (
          .let𝕔 (.store₁ x₁ x₄) (close₀ 5 X))))))))))))
  apply ctx𝕄.consℝ (fun X => .let𝕔 (.lit 1) (close₀ 0 X))
  apply ctxℝ.let𝕔; constructor
  apply ctx𝕄.consℝ (fun X => .let𝕔 (.alloc₁ x₀) (close₀ 1 X))
  apply ctxℝ.let𝕔; constructor
  apply ctx𝕄.consℝ (fun X => .lam𝕔 (close₀ 2 X))
  apply ctxℝ.lam𝕔
  apply ctx𝕄.consℝ (fun X => .let𝕔 (.load₁ x₁) (close₀ 3 X))
  apply ctxℝ.let𝕔; constructor
  apply ctx𝕄.consℝ (fun X => .let𝕔 (.binary₁ .mul x₂ x₃) (close₀ 4 X))
  apply ctxℝ.let𝕔; constructor; constructor; constructor
  apply ctx𝕄.consℝ (fun X => .let𝕔 (.store₁ x₁ x₄) (close₀ 5 X))
  apply ctxℝ.let𝕔; repeat constructor

example : step ([], expr𝕩𝕩₁) ([], expr𝕩𝕩₂) := by
  apply step_lvl.step𝕄
    (fun X =>
      .let𝕔 (.lit 1) (close₀ 0 (
      .let𝕔 (.alloc₁ x₀) (close₀ 1 (
        .lam𝕔 (close₀ 2 (
          .let𝕔 (.load₁ x₁) (close₀ 3 (
          .let𝕔 (.binary₁ .mul x₂ x₃) (close₀ 4 (
          .let𝕔 (.store₁ x₁ x₄) (close₀ 5 X))))))))))))
  apply ctx𝕄.consℝ (fun X => .let𝕔 (.lit 1) (close₀ 0 X))
  apply ctxℝ.let𝕔; constructor
  apply ctx𝕄.consℝ (fun X => .let𝕔 (.alloc₁ x₀) (close₀ 1 X))
  apply ctxℝ.let𝕔; constructor
  apply ctx𝕄.consℝ (fun X => .lam𝕔 (close₀ 2 X))
  apply ctxℝ.lam𝕔
  apply ctx𝕄.consℝ (fun X => .let𝕔 (.load₁ x₁) (close₀ 3 X))
  apply ctxℝ.let𝕔; constructor
  apply ctx𝕄.consℝ (fun X => .let𝕔 (.binary₁ .mul x₂ x₃) (close₀ 4 X))
  apply ctxℝ.let𝕔; constructor; constructor; constructor
  apply ctx𝕄.consℝ (fun X => .let𝕔 (.store₁ x₁ x₄) (close₀ 5 X))
  apply ctxℝ.let𝕔; repeat constructor

example : step ([], expr𝕩𝕩₂) ([], expr𝕩𝕩₃) := by
  apply step_lvl.step𝕄
    (fun X =>
      .let𝕔 (.lit 1) (close₀ 0 (
      .let𝕔 (.alloc₁ x₀) (close₀ 1 (
        .lam𝕔 (close₀ 2 (
          .let𝕔 (.load₁ x₁) (close₀ 3 (
          .let𝕔 (.binary₁ .mul x₂ x₃) (close₀ 4 (
          .let𝕔 (.store₁ x₁ x₄) (close₀ 5 (
          .lets (.store₂ (.code x₁) (.binary₂ .mul (.code x₂) X)) _)))))))))))))
  apply ctx𝕄.consℝ (fun X => .let𝕔 (.lit 1) (close₀ 0 X))
  apply ctxℝ.let𝕔; constructor
  apply ctx𝕄.consℝ (fun X => .let𝕔 (.alloc₁ x₀) (close₀ 1 X))
  apply ctxℝ.let𝕔; constructor
  apply ctx𝕄.consℝ (fun X => .lam𝕔 (close₀ 2 X))
  apply ctxℝ.lam𝕔
  apply ctx𝕄.consℝ (fun X => .let𝕔 (.load₁ x₁) (close₀ 3 X))
  apply ctxℝ.let𝕔; constructor
  apply ctx𝕄.consℝ (fun X => .let𝕔 (.binary₁ .mul x₂ x₃) (close₀ 4 X))
  apply ctxℝ.let𝕔; constructor; constructor; constructor
  apply ctx𝕄.consℝ (fun X => .let𝕔 (.store₁ x₁ x₄) (close₀ 5 X))
  apply ctxℝ.let𝕔; repeat constructor
  apply ctx𝕄.cons𝔹 (fun X => .lets X _)
  repeat constructor

example : step ([], expr𝕩𝕩₃) ([], expr𝕩𝕩₄) := by
  apply step_lvl.reflect
    (fun X =>
      .let𝕔 (.lit 1) (close₀ 0 (
      .let𝕔 (.alloc₁ x₀) (close₀ 1 (
        .lam𝕔 (close₀ 2 (
          .let𝕔 (.load₁ x₁) (close₀ 3 (
          .let𝕔 (.binary₁ .mul x₂ x₃) (close₀ 4 (
          .let𝕔 (.store₁ x₁ x₄) (close₀ 5 (
          X)))))))))))))
    (fun X => .lets (.store₂ (.code x₁) (.binary₂ .mul (.code x₂) X)) _)
  apply ctxℙ.consℚ
  apply ctxℚ.consℝ (fun X => .let𝕔 (.lit 1) (close₀ 0 X))
  apply ctxℝ.let𝕔; constructor
  apply ctxℚ.consℝ (fun X => .let𝕔 (.alloc₁ x₀) (close₀ 1 X))
  apply ctxℝ.let𝕔; constructor
  apply ctxℚ.consℝ (fun X => .lam𝕔 (close₀ 2 X))
  apply ctxℝ.lam𝕔
  apply ctxℚ.consℝ (fun X => .let𝕔 (.load₁ x₁) (close₀ 3 X))
  apply ctxℝ.let𝕔; constructor
  apply ctxℚ.consℝ (fun X => .let𝕔 (.binary₁ .mul x₂ x₃) (close₀ 4 X))
  apply ctxℝ.let𝕔; constructor; constructor; constructor
  apply ctxℚ.holeℝ (fun X => .let𝕔 (.store₁ x₁ x₄) (close₀ 5 X))
  apply ctxℝ.let𝕔; repeat constructor
  apply ctx𝔼.cons𝔹 (fun X => .lets X _)
  repeat constructor

example : step ([], expr𝕩𝕩₄) ([], expr𝕩𝕩₅) := by
  apply step_lvl.step𝕄
    (fun X =>
      .let𝕔 (.lit 1) (close₀ 0 (
      .let𝕔 (.alloc₁ x₀) (close₀ 1 (
        .lam𝕔 (close₀ 2 (
          .let𝕔 (.load₁ x₁) (close₀ 3 (
          .let𝕔 (.binary₁ .mul x₂ x₃) (close₀ 4 (
          .let𝕔 (.store₁ x₁ x₄) (close₀ 5 (
          .let𝕔 (.load₁ x₁) (close₀ 6 (
          .lets (.store₂ (.code x₁) X) _)))))))))))))))
  apply ctx𝕄.consℝ (fun X => .let𝕔 (.lit 1) (close₀ 0 X))
  apply ctxℝ.let𝕔; constructor
  apply ctx𝕄.consℝ (fun X => .let𝕔 (.alloc₁ x₀) (close₀ 1 X))
  apply ctxℝ.let𝕔; constructor
  apply ctx𝕄.consℝ (fun X => .lam𝕔 (close₀ 2 X))
  apply ctxℝ.lam𝕔
  apply ctx𝕄.consℝ (fun X => .let𝕔 (.load₁ x₁) (close₀ 3 X))
  apply ctxℝ.let𝕔; constructor
  apply ctx𝕄.consℝ (fun X => .let𝕔 (.binary₁ .mul x₂ x₃) (close₀ 4 X))
  apply ctxℝ.let𝕔; constructor; constructor; constructor
  apply ctx𝕄.consℝ (fun X => .let𝕔 (.store₁ x₁ x₄) (close₀ 5 X))
  apply ctxℝ.let𝕔; constructor; constructor; constructor
  apply ctx𝕄.consℝ (fun X => .let𝕔 (.load₁ x₁) (close₀ 6 X))
  apply ctxℝ.let𝕔; repeat constructor
  apply ctx𝕄.cons𝔹 (fun X => .lets X _)
  repeat constructor

example : step ([], expr𝕩𝕩₅) ([], expr𝕩𝕩₆) := by
  apply step_lvl.reflect
    (fun X =>
      .let𝕔 (.lit 1) (close₀ 0 (
      .let𝕔 (.alloc₁ x₀) (close₀ 1 (
        .lam𝕔 (close₀ 2 (
          .let𝕔 (.load₁ x₁) (close₀ 3 (
          .let𝕔 (.binary₁ .mul x₂ x₃) (close₀ 4 (
          .let𝕔 (.store₁ x₁ x₄) (close₀ 5 (
          .let𝕔 (.load₁ x₁) (close₀ 6 X))))))))))))))
    (fun X => .lets (.store₂ (.code x₁) X) _)
  apply ctxℙ.consℚ
  apply ctxℚ.consℝ (fun X => .let𝕔 (.lit 1) (close₀ 0 X))
  apply ctxℝ.let𝕔; constructor
  apply ctxℚ.consℝ (fun X => .let𝕔 (.alloc₁ x₀) (close₀ 1 X))
  apply ctxℝ.let𝕔; constructor
  apply ctxℚ.consℝ (fun X => .lam𝕔 (close₀ 2 X))
  apply ctxℝ.lam𝕔
  apply ctxℚ.consℝ (fun X => .let𝕔 (.load₁ x₁) (close₀ 3 X))
  apply ctxℝ.let𝕔; constructor
  apply ctxℚ.consℝ (fun X => .let𝕔 (.binary₁ .mul x₂ x₃) (close₀ 4 X))
  apply ctxℝ.let𝕔; constructor; constructor; constructor
  apply ctxℚ.consℝ (fun X => .let𝕔 (.store₁ x₁ x₄) (close₀ 5 X))
  apply ctxℝ.let𝕔; constructor; constructor; constructor
  apply ctxℚ.holeℝ (fun X => .let𝕔 (.load₁ x₁) (close₀ 6 X))
  apply ctxℝ.let𝕔; constructor
  apply ctx𝔼.cons𝔹 (fun X => .lets X _)
  repeat constructor

example : step ([], expr𝕩𝕩₆) ([], expr𝕩𝕩₇) := by
  apply step_lvl.step𝕄
    (fun X =>
      .let𝕔 (.lit 1) (close₀ 0 (
      .let𝕔 (.alloc₁ x₀) (close₀ 1 (
        .lam𝕔 (close₀ 2 (
          .let𝕔 (.load₁ x₁) (close₀ 3 (
          .let𝕔 (.binary₁ .mul x₂ x₃) (close₀ 4 (
          .let𝕔 (.store₁ x₁ x₄) (close₀ 5 (
          .let𝕔 (.load₁ x₁) (close₀ 6 (
          .let𝕔 (.binary₁ .mul x₂ x₆) (close₀ 7 (
          .lets X _)))))))))))))))))
  apply ctx𝕄.consℝ (fun X => .let𝕔 (.lit 1) (close₀ 0 X))
  apply ctxℝ.let𝕔; constructor
  apply ctx𝕄.consℝ (fun X => .let𝕔 (.alloc₁ x₀) (close₀ 1 X))
  apply ctxℝ.let𝕔; constructor
  apply ctx𝕄.consℝ (fun X => .lam𝕔 (close₀ 2 X))
  apply ctxℝ.lam𝕔
  apply ctx𝕄.consℝ (fun X => .let𝕔 (.load₁ x₁) (close₀ 3 X))
  apply ctxℝ.let𝕔; constructor
  apply ctx𝕄.consℝ (fun X => .let𝕔 (.binary₁ .mul x₂ x₃) (close₀ 4 X))
  apply ctxℝ.let𝕔; constructor; constructor; constructor
  apply ctx𝕄.consℝ (fun X => .let𝕔 (.store₁ x₁ x₄) (close₀ 5 X))
  apply ctxℝ.let𝕔; constructor; constructor; constructor
  apply ctx𝕄.consℝ (fun X => .let𝕔 (.load₁ x₁) (close₀ 6 X))
  apply ctxℝ.let𝕔; constructor
  apply ctx𝕄.consℝ (fun X => .let𝕔 (.binary₁ .mul x₂ x₆) (close₀ 7 X))
  apply ctxℝ.let𝕔; constructor; constructor; constructor
  apply ctx𝕄.cons𝔹 (fun X => .lets X _)
  repeat constructor

example : step ([], expr𝕩𝕩₇) ([], expr𝕩𝕩₈) := by
  apply step_lvl.reflect
    (fun X =>
      .let𝕔 (.lit 1) (close₀ 0 (
      .let𝕔 (.alloc₁ x₀) (close₀ 1 (
        .lam𝕔 (close₀ 2 (
          .let𝕔 (.load₁ x₁) (close₀ 3 (
          .let𝕔 (.binary₁ .mul x₂ x₃) (close₀ 4 (
          .let𝕔 (.store₁ x₁ x₄) (close₀ 5 (
          .let𝕔 (.load₁ x₁) (close₀ 6 (
          .let𝕔 (.binary₁ .mul x₂ x₆) (close₀ 7 X))))))))))))))))
    (fun X => .lets X _)
  apply ctxℙ.consℚ
  apply ctxℚ.consℝ (fun X => .let𝕔 (.lit 1) (close₀ 0 X))
  apply ctxℝ.let𝕔; constructor
  apply ctxℚ.consℝ (fun X => .let𝕔 (.alloc₁ x₀) (close₀ 1 X))
  apply ctxℝ.let𝕔; constructor
  apply ctxℚ.consℝ (fun X => .lam𝕔 (close₀ 2 X))
  apply ctxℝ.lam𝕔
  apply ctxℚ.consℝ (fun X => .let𝕔 (.load₁ x₁) (close₀ 3 X))
  apply ctxℝ.let𝕔; constructor
  apply ctxℚ.consℝ (fun X => .let𝕔 (.binary₁ .mul x₂ x₃) (close₀ 4 X))
  apply ctxℝ.let𝕔; constructor; constructor; constructor
  apply ctxℚ.consℝ (fun X => .let𝕔 (.store₁ x₁ x₄) (close₀ 5 X))
  apply ctxℝ.let𝕔; constructor; constructor; constructor
  apply ctxℚ.consℝ (fun X => .let𝕔 (.load₁ x₁) (close₀ 6 X))
  apply ctxℝ.let𝕔; constructor
  apply ctxℚ.holeℝ (fun X => .let𝕔 (.binary₁ .mul x₂ x₆) (close₀ 7 X))
  apply ctxℝ.let𝕔; constructor; constructor; constructor
  apply ctx𝔼.cons𝔹 (fun X => .lets X _)
  repeat constructor

example : step ([], expr𝕩𝕩₈) ([], expr𝕩𝕩₉) := by
  apply step_lvl.step𝕄
    (fun X =>
      .let𝕔 (.lit 1) (close₀ 0 (
      .let𝕔 (.alloc₁ x₀) (close₀ 1 (
        .lam𝕔 (close₀ 2 (
          .let𝕔 (.load₁ x₁) (close₀ 3 (
          .let𝕔 (.binary₁ .mul x₂ x₃) (close₀ 4 (
          .let𝕔 (.store₁ x₁ x₄) (close₀ 5 (
          .let𝕔 (.load₁ x₁) (close₀ 6 (
          .let𝕔 (.binary₁ .mul x₂ x₆) (close₀ 7 (
          .let𝕔 (.store₁ x₁ x₇) (close₀ 8 X))))))))))))))))))
  apply ctx𝕄.consℝ (fun X => .let𝕔 (.lit 1) (close₀ 0 X))
  apply ctxℝ.let𝕔; constructor
  apply ctx𝕄.consℝ (fun X => .let𝕔 (.alloc₁ x₀) (close₀ 1 X))
  apply ctxℝ.let𝕔; constructor
  apply ctx𝕄.consℝ (fun X => .lam𝕔 (close₀ 2 X))
  apply ctxℝ.lam𝕔
  apply ctx𝕄.consℝ (fun X => .let𝕔 (.load₁ x₁) (close₀ 3 X))
  apply ctxℝ.let𝕔; constructor
  apply ctx𝕄.consℝ (fun X => .let𝕔 (.binary₁ .mul x₂ x₃) (close₀ 4 X))
  apply ctxℝ.let𝕔; constructor; constructor; constructor
  apply ctx𝕄.consℝ (fun X => .let𝕔 (.store₁ x₁ x₄) (close₀ 5 X))
  apply ctxℝ.let𝕔; constructor; constructor; constructor
  apply ctx𝕄.consℝ (fun X => .let𝕔 (.load₁ x₁) (close₀ 6 X))
  apply ctxℝ.let𝕔; constructor
  apply ctx𝕄.consℝ (fun X => .let𝕔 (.binary₁ .mul x₂ x₆) (close₀ 7 X))
  apply ctxℝ.let𝕔; constructor; constructor; constructor
  apply ctx𝕄.consℝ (fun X => .let𝕔 (.store₁ x₁ x₇) (close₀ 8 X))
  apply ctxℝ.let𝕔; constructor; constructor; constructor
  repeat constructor

example : step ([], expr𝕩𝕩₉) ([], expr𝕩𝕩𝕩₀) := by
  apply step_lvl.step𝕄
    (fun X =>
      .let𝕔 (.lit 1) (close₀ 0 (
      .let𝕔 (.alloc₁ x₀) (close₀ 1 (
        .lam𝕔 (close₀ 2 (
          .let𝕔 (.load₁ x₁) (close₀ 3 (
          .let𝕔 (.binary₁ .mul x₂ x₃) (close₀ 4 (
          .let𝕔 (.store₁ x₁ x₄) (close₀ 5 (
          .let𝕔 (.load₁ x₁) (close₀ 6 (
          .let𝕔 (.binary₁ .mul x₂ x₆) (close₀ 7 (
          .let𝕔 (.store₁ x₁ x₇) (close₀ 8 (
          .app₁ X _)))))))))))))))))))
  apply ctx𝕄.consℝ (fun X => .let𝕔 (.lit 1) (close₀ 0 X))
  apply ctxℝ.let𝕔; constructor
  apply ctx𝕄.consℝ (fun X => .let𝕔 (.alloc₁ x₀) (close₀ 1 X))
  apply ctxℝ.let𝕔; constructor
  apply ctx𝕄.consℝ (fun X => .lam𝕔 (close₀ 2 X))
  apply ctxℝ.lam𝕔
  apply ctx𝕄.consℝ (fun X => .let𝕔 (.load₁ x₁) (close₀ 3 X))
  apply ctxℝ.let𝕔; constructor
  apply ctx𝕄.consℝ (fun X => .let𝕔 (.binary₁ .mul x₂ x₃) (close₀ 4 X))
  apply ctxℝ.let𝕔; constructor; constructor; constructor
  apply ctx𝕄.consℝ (fun X => .let𝕔 (.store₁ x₁ x₄) (close₀ 5 X))
  apply ctxℝ.let𝕔; constructor; constructor; constructor
  apply ctx𝕄.consℝ (fun X => .let𝕔 (.load₁ x₁) (close₀ 6 X))
  apply ctxℝ.let𝕔; constructor
  apply ctx𝕄.consℝ (fun X => .let𝕔 (.binary₁ .mul x₂ x₆) (close₀ 7 X))
  apply ctxℝ.let𝕔; constructor; constructor; constructor
  apply ctx𝕄.consℝ (fun X => .let𝕔 (.store₁ x₁ x₇) (close₀ 8 X))
  apply ctxℝ.let𝕔; constructor; constructor; constructor
  apply ctx𝕄.cons𝔹 (fun X => .app₁ X _)
  repeat constructor

example : step ([], expr𝕩𝕩𝕩₀) ([], expr𝕩𝕩𝕩₁) := by
  let left : Expr :=
    .lam (close₀ 104 (
      .ifz₁ n (
        .load₂ (.code x₁)) (
        .lets (.store₂ (.code x₁) (.binary₂ .mul (.code x₂) (.load₂ (.code x₁)))) (
        .app₁ (
          .fix₁ (
            .lam (close₀ 103 (
            .lam (close₀ 104 (
              .ifz₁ n (
                .load₂ (.code x₁)) (
                .lets (.store₂ (.code x₁) (.binary₂ .mul (.code x₂) (.load₂ (.code x₁)))) (
                .app₁ f (.binary₁ .sub n (.lit 1)))))))))) (
          .binary₁ .sub n (.lit 1))))))
  apply step_lvl.step𝕄
    (fun X =>
      .let𝕔 (.lit 1) (close₀ 0 (
      .let𝕔 (.alloc₁ x₀) (close₀ 1 (
        .lam𝕔 (close₀ 2 (
          .let𝕔 (.load₁ x₁) (close₀ 3 (
          .let𝕔 (.binary₁ .mul x₂ x₃) (close₀ 4 (
          .let𝕔 (.store₁ x₁ x₄) (close₀ 5 (
          .let𝕔 (.load₁ x₁) (close₀ 6 (
          .let𝕔 (.binary₁ .mul x₂ x₆) (close₀ 7 (
          .let𝕔 (.store₁ x₁ x₇) (close₀ 8 (
          .app₁ left X)))))))))))))))))))
  apply ctx𝕄.consℝ (fun X => .let𝕔 (.lit 1) (close₀ 0 X))
  apply ctxℝ.let𝕔; constructor
  apply ctx𝕄.consℝ (fun X => .let𝕔 (.alloc₁ x₀) (close₀ 1 X))
  apply ctxℝ.let𝕔; constructor
  apply ctx𝕄.consℝ (fun X => .lam𝕔 (close₀ 2 X))
  apply ctxℝ.lam𝕔
  apply ctx𝕄.consℝ (fun X => .let𝕔 (.load₁ x₁) (close₀ 3 X))
  apply ctxℝ.let𝕔; constructor
  apply ctx𝕄.consℝ (fun X => .let𝕔 (.binary₁ .mul x₂ x₃) (close₀ 4 X))
  apply ctxℝ.let𝕔; constructor; constructor; constructor
  apply ctx𝕄.consℝ (fun X => .let𝕔 (.store₁ x₁ x₄) (close₀ 5 X))
  apply ctxℝ.let𝕔; constructor; constructor; constructor
  apply ctx𝕄.consℝ (fun X => .let𝕔 (.load₁ x₁) (close₀ 6 X))
  apply ctxℝ.let𝕔; constructor
  apply ctx𝕄.consℝ (fun X => .let𝕔 (.binary₁ .mul x₂ x₆) (close₀ 7 X))
  apply ctxℝ.let𝕔; constructor; constructor; constructor
  apply ctx𝕄.consℝ (fun X => .let𝕔 (.store₁ x₁ x₇) (close₀ 8 X))
  apply ctxℝ.let𝕔; constructor; constructor; constructor
  apply ctx𝕄.cons𝔹 (fun X => .app₁ left X)
  repeat constructor

example : step ([], expr𝕩𝕩𝕩₁) ([], expr𝕩𝕩𝕩₂) := by
  apply step_lvl.step𝕄
    (fun X =>
      .let𝕔 (.lit 1) (close₀ 0 (
      .let𝕔 (.alloc₁ x₀) (close₀ 1 (
        .lam𝕔 (close₀ 2 (
          .let𝕔 (.load₁ x₁) (close₀ 3 (
          .let𝕔 (.binary₁ .mul x₂ x₃) (close₀ 4 (
          .let𝕔 (.store₁ x₁ x₄) (close₀ 5 (
          .let𝕔 (.load₁ x₁) (close₀ 6 (
          .let𝕔 (.binary₁ .mul x₂ x₆) (close₀ 7 (
          .let𝕔 (.store₁ x₁ x₇) (close₀ 8 X))))))))))))))))))
  apply ctx𝕄.consℝ (fun X => .let𝕔 (.lit 1) (close₀ 0 X))
  apply ctxℝ.let𝕔; constructor
  apply ctx𝕄.consℝ (fun X => .let𝕔 (.alloc₁ x₀) (close₀ 1 X))
  apply ctxℝ.let𝕔; constructor
  apply ctx𝕄.consℝ (fun X => .lam𝕔 (close₀ 2 X))
  apply ctxℝ.lam𝕔
  apply ctx𝕄.consℝ (fun X => .let𝕔 (.load₁ x₁) (close₀ 3 X))
  apply ctxℝ.let𝕔; constructor
  apply ctx𝕄.consℝ (fun X => .let𝕔 (.binary₁ .mul x₂ x₃) (close₀ 4 X))
  apply ctxℝ.let𝕔; constructor; constructor; constructor
  apply ctx𝕄.consℝ (fun X => .let𝕔 (.store₁ x₁ x₄) (close₀ 5 X))
  apply ctxℝ.let𝕔; constructor; constructor; constructor
  apply ctx𝕄.consℝ (fun X => .let𝕔 (.load₁ x₁) (close₀ 6 X))
  apply ctxℝ.let𝕔; constructor
  apply ctx𝕄.consℝ (fun X => .let𝕔 (.binary₁ .mul x₂ x₆) (close₀ 7 X))
  apply ctxℝ.let𝕔; constructor; constructor; constructor
  apply ctx𝕄.consℝ (fun X => .let𝕔 (.store₁ x₁ x₇) (close₀ 8 X))
  apply ctxℝ.let𝕔; constructor; constructor; constructor
  repeat constructor

example : step ([], expr𝕩𝕩𝕩₂) ([], expr𝕩𝕩𝕩₃) := by
  apply step_lvl.step𝕄
    (fun X =>
      .let𝕔 (.lit 1) (close₀ 0 (
      .let𝕔 (.alloc₁ x₀) (close₀ 1 (
        .lam𝕔 (close₀ 2 (
          .let𝕔 (.load₁ x₁) (close₀ 3 (
          .let𝕔 (.binary₁ .mul x₂ x₃) (close₀ 4 (
          .let𝕔 (.store₁ x₁ x₄) (close₀ 5 (
          .let𝕔 (.load₁ x₁) (close₀ 6 (
          .let𝕔 (.binary₁ .mul x₂ x₆) (close₀ 7 (
          .let𝕔 (.store₁ x₁ x₇) (close₀ 8 X))))))))))))))))))
  apply ctx𝕄.consℝ (fun X => .let𝕔 (.lit 1) (close₀ 0 X))
  apply ctxℝ.let𝕔; constructor
  apply ctx𝕄.consℝ (fun X => .let𝕔 (.alloc₁ x₀) (close₀ 1 X))
  apply ctxℝ.let𝕔; constructor
  apply ctx𝕄.consℝ (fun X => .lam𝕔 (close₀ 2 X))
  apply ctxℝ.lam𝕔
  apply ctx𝕄.consℝ (fun X => .let𝕔 (.load₁ x₁) (close₀ 3 X))
  apply ctxℝ.let𝕔; constructor
  apply ctx𝕄.consℝ (fun X => .let𝕔 (.binary₁ .mul x₂ x₃) (close₀ 4 X))
  apply ctxℝ.let𝕔; constructor; constructor; constructor
  apply ctx𝕄.consℝ (fun X => .let𝕔 (.store₁ x₁ x₄) (close₀ 5 X))
  apply ctxℝ.let𝕔; constructor; constructor; constructor
  apply ctx𝕄.consℝ (fun X => .let𝕔 (.load₁ x₁) (close₀ 6 X))
  apply ctxℝ.let𝕔; constructor
  apply ctx𝕄.consℝ (fun X => .let𝕔 (.binary₁ .mul x₂ x₆) (close₀ 7 X))
  apply ctxℝ.let𝕔; constructor; constructor; constructor
  apply ctx𝕄.consℝ (fun X => .let𝕔 (.store₁ x₁ x₇) (close₀ 8 X))
  apply ctxℝ.let𝕔; constructor; constructor; constructor
  repeat constructor

example : step ([], expr𝕩𝕩𝕩₃) ([], expr𝕩𝕩𝕩₄) := by
  apply step_lvl.step𝕄
    (fun X =>
      .let𝕔 (.lit 1) (close₀ 0 (
      .let𝕔 (.alloc₁ x₀) (close₀ 1 (
        .lam𝕔 (close₀ 2 (
          .let𝕔 (.load₁ x₁) (close₀ 3 (
          .let𝕔 (.binary₁ .mul x₂ x₃) (close₀ 4 (
          .let𝕔 (.store₁ x₁ x₄) (close₀ 5 (
          .let𝕔 (.load₁ x₁) (close₀ 6 (
          .let𝕔 (.binary₁ .mul x₂ x₆) (close₀ 7 (
          .let𝕔 (.store₁ x₁ x₇) (close₀ 8 X))))))))))))))))))
  apply ctx𝕄.consℝ (fun X => .let𝕔 (.lit 1) (close₀ 0 X))
  apply ctxℝ.let𝕔; constructor
  apply ctx𝕄.consℝ (fun X => .let𝕔 (.alloc₁ x₀) (close₀ 1 X))
  apply ctxℝ.let𝕔; constructor
  apply ctx𝕄.consℝ (fun X => .lam𝕔 (close₀ 2 X))
  apply ctxℝ.lam𝕔
  apply ctx𝕄.consℝ (fun X => .let𝕔 (.load₁ x₁) (close₀ 3 X))
  apply ctxℝ.let𝕔; constructor
  apply ctx𝕄.consℝ (fun X => .let𝕔 (.binary₁ .mul x₂ x₃) (close₀ 4 X))
  apply ctxℝ.let𝕔; constructor; constructor; constructor
  apply ctx𝕄.consℝ (fun X => .let𝕔 (.store₁ x₁ x₄) (close₀ 5 X))
  apply ctxℝ.let𝕔; constructor; constructor; constructor
  apply ctx𝕄.consℝ (fun X => .let𝕔 (.load₁ x₁) (close₀ 6 X))
  apply ctxℝ.let𝕔; constructor
  apply ctx𝕄.consℝ (fun X => .let𝕔 (.binary₁ .mul x₂ x₆) (close₀ 7 X))
  apply ctxℝ.let𝕔; constructor; constructor; constructor
  apply ctx𝕄.consℝ (fun X => .let𝕔 (.store₁ x₁ x₇) (close₀ 8 X))
  apply ctxℝ.let𝕔; constructor; constructor; constructor
  repeat constructor

example : step ([], expr𝕩𝕩𝕩₄) ([], expr𝕩𝕩𝕩₅) := by
  apply step_lvl.reflect
    (fun X =>
      .let𝕔 (.lit 1) (close₀ 0 (
      .let𝕔 (.alloc₁ x₀) (close₀ 1 (
        .lam𝕔 (close₀ 2 (
          .let𝕔 (.load₁ x₁) (close₀ 3 (
          .let𝕔 (.binary₁ .mul x₂ x₃) (close₀ 4 (
          .let𝕔 (.store₁ x₁ x₄) (close₀ 5 (
          .let𝕔 (.load₁ x₁) (close₀ 6 (
          .let𝕔 (.binary₁ .mul x₂ x₆) (close₀ 7 (
          .let𝕔 (.store₁ x₁ x₇) (close₀ 8 X))))))))))))))))))
    id
  apply ctxℙ.consℚ
  apply ctxℚ.consℝ (fun X => .let𝕔 (.lit 1) (close₀ 0 X))
  apply ctxℝ.let𝕔; constructor
  apply ctxℚ.consℝ (fun X => .let𝕔 (.alloc₁ x₀) (close₀ 1 X))
  apply ctxℝ.let𝕔; constructor
  apply ctxℚ.consℝ (fun X => .lam𝕔 (close₀ 2 X))
  apply ctxℝ.lam𝕔
  apply ctxℚ.consℝ (fun X => .let𝕔 (.load₁ x₁) (close₀ 3 X))
  apply ctxℝ.let𝕔; constructor
  apply ctxℚ.consℝ (fun X => .let𝕔 (.binary₁ .mul x₂ x₃) (close₀ 4 X))
  apply ctxℝ.let𝕔; constructor; constructor; constructor
  apply ctxℚ.consℝ (fun X => .let𝕔 (.store₁ x₁ x₄) (close₀ 5 X))
  apply ctxℝ.let𝕔; constructor; constructor; constructor
  apply ctxℚ.consℝ (fun X => .let𝕔 (.load₁ x₁) (close₀ 6 X))
  apply ctxℝ.let𝕔; constructor
  apply ctxℚ.consℝ (fun X => .let𝕔 (.binary₁ .mul x₂ x₆) (close₀ 7 X))
  apply ctxℝ.let𝕔; constructor; constructor; constructor
  apply ctxℚ.holeℝ (fun X => .let𝕔 (.store₁ x₁ x₇) (close₀ 8 X))
  apply ctxℝ.let𝕔; constructor; constructor; constructor
  repeat constructor

example : step ([], expr𝕩𝕩𝕩₅) ([], expr𝕩𝕩𝕩₆) := by
  apply step_lvl.step𝕄
    (fun X =>
      .let𝕔 (.lit 1) (close₀ 0 (
      .let𝕔 (.alloc₁ x₀) (close₀ 1 (
        .lam𝕔 (close₀ 2 (
          .let𝕔 (.load₁ x₁) (close₀ 3 (
          .let𝕔 (.binary₁ .mul x₂ x₃) (close₀ 4 (
          .let𝕔 (.store₁ x₁ x₄) (close₀ 5 (
          .let𝕔 (.load₁ x₁) (close₀ 6 (
          .let𝕔 (.binary₁ .mul x₂ x₆) (close₀ 7 (
          .let𝕔 (.store₁ x₁ x₇) (close₀ 8 X))))))))))))))))))
  apply ctx𝕄.consℝ (fun X => .let𝕔 (.lit 1) (close₀ 0 X))
  apply ctxℝ.let𝕔; constructor
  apply ctx𝕄.consℝ (fun X => .let𝕔 (.alloc₁ x₀) (close₀ 1 X))
  apply ctxℝ.let𝕔; constructor
  apply ctx𝕄.consℝ (fun X => .lam𝕔 (close₀ 2 X))
  apply ctxℝ.lam𝕔
  apply ctx𝕄.consℝ (fun X => .let𝕔 (.load₁ x₁) (close₀ 3 X))
  apply ctxℝ.let𝕔; constructor
  apply ctx𝕄.consℝ (fun X => .let𝕔 (.binary₁ .mul x₂ x₃) (close₀ 4 X))
  apply ctxℝ.let𝕔; constructor; constructor; constructor
  apply ctx𝕄.consℝ (fun X => .let𝕔 (.store₁ x₁ x₄) (close₀ 5 X))
  apply ctxℝ.let𝕔; constructor; constructor; constructor
  apply ctx𝕄.consℝ (fun X => .let𝕔 (.load₁ x₁) (close₀ 6 X))
  apply ctxℝ.let𝕔; constructor
  apply ctx𝕄.consℝ (fun X => .let𝕔 (.binary₁ .mul x₂ x₆) (close₀ 7 X))
  apply ctxℝ.let𝕔; constructor; constructor; constructor
  apply ctx𝕄.consℝ (fun X => .let𝕔 (.store₁ x₁ x₇) (close₀ 8 X))
  apply ctxℝ.let𝕔; constructor; constructor; constructor
  repeat constructor

example : step ([], expr𝕩𝕩𝕩₆) ([], expr𝕩𝕩𝕩₇) := by
  apply step_lvl.step𝕄
    (fun X =>
      .let𝕔 (.lit 1) (close₀ 0 (
      .let𝕔 (.alloc₁ x₀) (close₀ 1 (
        .lam𝕔 (close₀ 2 (
          .let𝕔 (.load₁ x₁) (close₀ 3 (
          .let𝕔 (.binary₁ .mul x₂ x₃) (close₀ 4 (
          .let𝕔 (.store₁ x₁ x₄) (close₀ 5 (
          .let𝕔 (.load₁ x₁) (close₀ 6 (
          .let𝕔 (.binary₁ .mul x₂ x₆) (close₀ 7 X))))))))))))))))
  apply ctx𝕄.consℝ (fun X => .let𝕔 (.lit 1) (close₀ 0 X))
  apply ctxℝ.let𝕔; constructor
  apply ctx𝕄.consℝ (fun X => .let𝕔 (.alloc₁ x₀) (close₀ 1 X))
  apply ctxℝ.let𝕔; constructor
  apply ctx𝕄.consℝ (fun X => .lam𝕔 (close₀ 2 X))
  apply ctxℝ.lam𝕔
  apply ctx𝕄.consℝ (fun X => .let𝕔 (.load₁ x₁) (close₀ 3 X))
  apply ctxℝ.let𝕔; constructor
  apply ctx𝕄.consℝ (fun X => .let𝕔 (.binary₁ .mul x₂ x₃) (close₀ 4 X))
  apply ctxℝ.let𝕔; constructor; constructor; constructor
  apply ctx𝕄.consℝ (fun X => .let𝕔 (.store₁ x₁ x₄) (close₀ 5 X))
  apply ctxℝ.let𝕔; constructor; constructor; constructor
  apply ctx𝕄.consℝ (fun X => .let𝕔 (.load₁ x₁) (close₀ 6 X))
  apply ctxℝ.let𝕔; constructor
  apply ctx𝕄.consℝ (fun X => .let𝕔 (.binary₁ .mul x₂ x₆) (close₀ 7 X))
  apply ctxℝ.let𝕔; constructor; constructor; constructor
  repeat constructor

example : step ([], expr𝕩𝕩𝕩₇) ([], expr𝕩𝕩𝕩₈) := by
  apply step_lvl.step𝕄
    (fun X =>
      .let𝕔 (.lit 1) (close₀ 0 (
      .let𝕔 (.alloc₁ x₀) (close₀ 1 (
        .lam𝕔 (close₀ 2 (
          .let𝕔 (.load₁ x₁) (close₀ 3 (
          .let𝕔 (.binary₁ .mul x₂ x₃) (close₀ 4 (
          .let𝕔 (.store₁ x₁ x₄) (close₀ 5 (
          .let𝕔 (.load₁ x₁) (close₀ 6 X))))))))))))))
  apply ctx𝕄.consℝ (fun X => .let𝕔 (.lit 1) (close₀ 0 X))
  apply ctxℝ.let𝕔; constructor
  apply ctx𝕄.consℝ (fun X => .let𝕔 (.alloc₁ x₀) (close₀ 1 X))
  apply ctxℝ.let𝕔; constructor
  apply ctx𝕄.consℝ (fun X => .lam𝕔 (close₀ 2 X))
  apply ctxℝ.lam𝕔
  apply ctx𝕄.consℝ (fun X => .let𝕔 (.load₁ x₁) (close₀ 3 X))
  apply ctxℝ.let𝕔; constructor
  apply ctx𝕄.consℝ (fun X => .let𝕔 (.binary₁ .mul x₂ x₃) (close₀ 4 X))
  apply ctxℝ.let𝕔; constructor; constructor; constructor
  apply ctx𝕄.consℝ (fun X => .let𝕔 (.store₁ x₁ x₄) (close₀ 5 X))
  apply ctxℝ.let𝕔; constructor; constructor; constructor
  apply ctx𝕄.consℝ (fun X => .let𝕔 (.load₁ x₁) (close₀ 6 X))
  apply ctxℝ.let𝕔; constructor
  repeat constructor

example : step ([], expr𝕩𝕩𝕩₈) ([], expr𝕩𝕩𝕩₉) := by
  apply step_lvl.step𝕄
    (fun X =>
      .let𝕔 (.lit 1) (close₀ 0 (
      .let𝕔 (.alloc₁ x₀) (close₀ 1 (
        .lam𝕔 (close₀ 2 (
          .let𝕔 (.load₁ x₁) (close₀ 3 (
          .let𝕔 (.binary₁ .mul x₂ x₃) (close₀ 4 (
          .let𝕔 (.store₁ x₁ x₄) (close₀ 5 X))))))))))))
  apply ctx𝕄.consℝ (fun X => .let𝕔 (.lit 1) (close₀ 0 X))
  apply ctxℝ.let𝕔; constructor
  apply ctx𝕄.consℝ (fun X => .let𝕔 (.alloc₁ x₀) (close₀ 1 X))
  apply ctxℝ.let𝕔; constructor
  apply ctx𝕄.consℝ (fun X => .lam𝕔 (close₀ 2 X))
  apply ctxℝ.lam𝕔
  apply ctx𝕄.consℝ (fun X => .let𝕔 (.load₁ x₁) (close₀ 3 X))
  apply ctxℝ.let𝕔; constructor
  apply ctx𝕄.consℝ (fun X => .let𝕔 (.binary₁ .mul x₂ x₃) (close₀ 4 X))
  apply ctxℝ.let𝕔; constructor; constructor; constructor
  apply ctx𝕄.consℝ (fun X => .let𝕔 (.store₁ x₁ x₄) (close₀ 5 X))
  apply ctxℝ.let𝕔; constructor; constructor; constructor
  repeat constructor

example : step ([], expr𝕩𝕩𝕩₉) ([], expr𝕩𝕩𝕩𝕩₀) := by
  apply step_lvl.step𝕄
    (fun X =>
      .let𝕔 (.lit 1) (close₀ 0 (
      .let𝕔 (.alloc₁ x₀) (close₀ 1 (
        .lam𝕔 (close₀ 2 (
          .let𝕔 (.load₁ x₁) (close₀ 3 (
          .let𝕔 (.binary₁ .mul x₂ x₃) (close₀ 4 X))))))))))
  apply ctx𝕄.consℝ (fun X => .let𝕔 (.lit 1) (close₀ 0 X))
  apply ctxℝ.let𝕔; constructor
  apply ctx𝕄.consℝ (fun X => .let𝕔 (.alloc₁ x₀) (close₀ 1 X))
  apply ctxℝ.let𝕔; constructor
  apply ctx𝕄.consℝ (fun X => .lam𝕔 (close₀ 2 X))
  apply ctxℝ.lam𝕔
  apply ctx𝕄.consℝ (fun X => .let𝕔 (.load₁ x₁) (close₀ 3 X))
  apply ctxℝ.let𝕔; constructor
  apply ctx𝕄.consℝ (fun X => .let𝕔 (.binary₁ .mul x₂ x₃) (close₀ 4 X))
  apply ctxℝ.let𝕔; constructor; constructor; constructor
  repeat constructor

example : step ([], expr𝕩𝕩𝕩𝕩₀) ([], expr𝕩𝕩𝕩𝕩₁) := by
  apply step_lvl.step𝕄
    (fun X =>
      .let𝕔 (.lit 1) (close₀ 0 (
      .let𝕔 (.alloc₁ x₀) (close₀ 1 (
        .lam𝕔 (close₀ 2 (
          .let𝕔 (.load₁ x₁) (close₀ 3 X))))))))
  apply ctx𝕄.consℝ (fun X => .let𝕔 (.lit 1) (close₀ 0 X))
  apply ctxℝ.let𝕔; constructor
  apply ctx𝕄.consℝ (fun X => .let𝕔 (.alloc₁ x₀) (close₀ 1 X))
  apply ctxℝ.let𝕔; constructor
  apply ctx𝕄.consℝ (fun X => .lam𝕔 (close₀ 2 X))
  apply ctxℝ.lam𝕔
  apply ctx𝕄.consℝ (fun X => .let𝕔 (.load₁ x₁) (close₀ 3 X))
  apply ctxℝ.let𝕔; constructor
  repeat constructor

example : step ([], expr𝕩𝕩𝕩𝕩₁) ([], expr𝕩𝕩𝕩𝕩₂) := by
  apply step_lvl.step𝕄
    (fun X =>
      .let𝕔 (.lit 1) (close₀ 0 (
      .let𝕔 (.alloc₁ x₀) (close₀ 1 (
        .lam𝕔 (close₀ 2 X))))))
  apply ctx𝕄.consℝ (fun X => .let𝕔 (.lit 1) (close₀ 0 X))
  apply ctxℝ.let𝕔; constructor
  apply ctx𝕄.consℝ (fun X => .let𝕔 (.alloc₁ x₀) (close₀ 1 X))
  apply ctxℝ.let𝕔; constructor
  apply ctx𝕄.consℝ (fun X => .lam𝕔 (close₀ 2 X))
  apply ctxℝ.lam𝕔
  repeat constructor

example : step ([], expr𝕩𝕩𝕩𝕩₂) ([], expr𝕩𝕩𝕩𝕩₃) := by
  apply step_lvl.step𝕄
    (fun X =>
      .let𝕔 (.lit 1) (close₀ 0 (
      .let𝕔 (.alloc₁ x₀) (close₀ 1 X))))
  apply ctx𝕄.consℝ (fun X => .let𝕔 (.lit 1) (close₀ 0 X))
  apply ctxℝ.let𝕔; constructor
  apply ctx𝕄.consℝ (fun X => .let𝕔 (.alloc₁ x₀) (close₀ 1 X))
  apply ctxℝ.let𝕔; constructor
  repeat constructor

example : step ([], expr𝕩𝕩𝕩𝕩₃) ([], expr𝕩𝕩𝕩𝕩₄) := by
  apply step_lvl.reflect
    (fun X =>
      .let𝕔 (.lit 1) (close₀ 0 (
      .let𝕔 (.alloc₁ x₀) (close₀ 1 X))))
    id
  apply ctxℙ.consℚ
  apply ctxℚ.consℝ (fun X => .let𝕔 (.lit 1) (close₀ 0 X))
  apply ctxℝ.let𝕔; constructor
  apply ctxℚ.holeℝ (fun X => .let𝕔 (.alloc₁ x₀) (close₀ 1 X))
  apply ctxℝ.let𝕔; constructor
  repeat constructor

example : step ([], expr𝕩𝕩𝕩𝕩₄) ([], expr𝕩𝕩𝕩𝕩₅) := by
  apply step_lvl.step𝕄
    (fun X =>
      .let𝕔 (.lit 1) (close₀ 0 (
      .let𝕔 (.alloc₁ x₀) (close₀ 1 X))))
  apply ctx𝕄.consℝ (fun X => .let𝕔 (.lit 1) (close₀ 0 X))
  apply ctxℝ.let𝕔; constructor
  apply ctx𝕄.consℝ (fun X => .let𝕔 (.alloc₁ x₀) (close₀ 1 X))
  apply ctxℝ.let𝕔; constructor
  repeat constructor

example : step ([], expr𝕩𝕩𝕩𝕩₅) ([], expr𝕩𝕩𝕩𝕩₆) := by
  apply step_lvl.step𝕄
    (fun X =>
      .let𝕔 (.lit 1) (close₀ 0 X))
  apply ctx𝕄.consℝ (fun X => .let𝕔 (.lit 1) (close₀ 0 X))
  apply ctxℝ.let𝕔; constructor
  repeat constructor

example : step ([], expr𝕩𝕩𝕩𝕩₆) ([], expr𝕩𝕩𝕩𝕩₇) := by
  apply step_lvl.step𝕄 id
  repeat constructor

set_option maxRecDepth 1000 in
example : typing_reification [] [] expr₀ (.rep (.arrow .nat .nat ∅)) .reify :=
  by
  rw [← union_reify_left .reify]; repeat constructor
  rw [← union_pure_left .reify]; repeat constructor
  rw [← union_reify_right .reify]; repeat constructor
  rw [← union_pure_right .reify, ← union_pure_right .reify]; repeat constructor
  rw [← union_pure_left ∅]; repeat constructor

set_option maxRecDepth 2000 in
example : typing_reification [] [] expr𝕩𝕩𝕩𝕩₇ (.rep (.arrow .nat .nat ∅)) ∅ :=
  by
  repeat
    first
    | constructor
    | rw [← union_pure_left ∅]
end StageMutablePower
