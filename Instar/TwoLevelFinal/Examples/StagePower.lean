import Instar.TwoLevelFinal.Examples.Notation

-- stage power function xⁿ
namespace StagePower

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
--
-- ⭢*
--
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
    .lam { 101 ⇛
      .fix₁ (
        .lam { 102 ⇛
        .lam { 103 ⇛
          .ifz₁ n (
            .lift (.lit 1)) (
            .binary₂ .mul x (.app₁ f (.binary₁ .sub n (.lit 1))))}})}) { 100 ⇛
  .lift (
    .lam { 104 ⇛
      .app₁ (.app₁ power y) (.lit 2)})}

def expr₁ : Expr :=
  .lift (
    .lam { 104 ⇛
      .app₁ (
        .app₁ (
          .lam { 101 ⇛
            .fix₁ (
              .lam { 102 ⇛
              .lam { 103 ⇛
                .ifz₁ n (
                  .lift (.lit 1)) (
                  .binary₂ .mul x (.app₁ f (.binary₁ .sub n (.lit 1))))}})})
          y) (
        .lit 2)})

def expr₂ : Expr :=
  .lam𝕔 { 0 ⇛
    .app₁ (
      .app₁ (
        .lam { 101 ⇛
          .fix₁ (
            .lam { 102 ⇛
            .lam { 103 ⇛
              .ifz₁ n (
                .lift (.lit 1)) (
                .binary₂ .mul x (.app₁ f (.binary₁ .sub n (.lit 1))))}})}) (
        .code x₀)) (
      .lit 2)}

def expr₃ : Expr :=
  .lam𝕔 { 0 ⇛
    .app₁ (
      .fix₁ (
        .lam { 102 ⇛
        .lam { 103 ⇛
          .ifz₁ n (
            .lift (.lit 1)) (
            .binary₂ .mul (.code x₀) (.app₁ f (.binary₁ .sub n (.lit 1))))}})) (
      .lit 2)}

def expr₄ : Expr :=
  .lam𝕔 { 0 ⇛
    .app₁ (
      .lam (
        .app₁ (
          .app₁ (
            .lam { 102 ⇛
            .lam { 103 ⇛
              .ifz₁ n (
                .lift (.lit 1)) (
                .binary₂ .mul (.code x₀) (.app₁ f (.binary₁ .sub n (.lit 1))))}}) (
            .fix₁ (
              .lam { 102 ⇛
              .lam { 103 ⇛
                .ifz₁ n (
                  .lift (.lit 1)) (
                  .binary₂ .mul (.code x₀) (.app₁ f (.binary₁ .sub n (.lit 1))))}}))) (
          .bvar 0))) (
      .lit 2)}

def expr₅ : Expr :=
  .lam𝕔 { 0 ⇛
    .app₁ (
      .app₁ (
        .lam { 102 ⇛
        .lam { 103 ⇛
          .ifz₁ n (
            .lift (.lit 1)) (
            .binary₂ .mul (.code x₀) (.app₁ f (.binary₁ .sub n (.lit 1))))}}) (
        .fix₁ (
          .lam { 102 ⇛
          .lam { 103 ⇛
            .ifz₁ n (
              .lift (.lit 1)) (
              .binary₂ .mul (.code x₀) (.app₁ f (.binary₁ .sub n (.lit 1))))}}))) (
      .lit 2)}

def expr₆ : Expr :=
  .lam𝕔 { 0 ⇛
    .app₁ (
      .app₁ (
        .lam { 102 ⇛
        .lam { 103 ⇛
          .ifz₁ n (
            .lift (.lit 1)) (
            .binary₂ .mul (.code x₀) (.app₁ f (.binary₁ .sub n (.lit 1))))}}) (
        .lam (
          .app₁ (
            .app₁ (
              .lam { 102 ⇛
              .lam { 103 ⇛
                .ifz₁ n (
                  .lift (.lit 1)) (
                  .binary₂ .mul (.code x₀) (.app₁ f (.binary₁ .sub n (.lit 1))))}}) (
              .fix₁ (
                .lam { 102 ⇛
                .lam { 103 ⇛
                  .ifz₁ n (
                    .lift (.lit 1)) (
                    .binary₂ .mul (.code x₀) (.app₁ f (.binary₁ .sub n (.lit 1))))}}))) (
            .bvar 0)))) (
      .lit 2)}

def expr₇ : Expr :=
  .lam𝕔 { 0 ⇛
    .app₁ (
      .lam { 103 ⇛
        .ifz₁ n (
          .lift (.lit 1)) (
          .binary₂ .mul (
            .code x₀) (
            .app₁ (
              .lam (
                .app₁ (
                  .app₁ (
                    .lam { 102 ⇛
                    .lam { 103 ⇛
                      .ifz₁ n (
                        .lift (.lit 1)) (
                        .binary₂ .mul (.code x₀) (.app₁ f (.binary₁ .sub n (.lit 1))))}}) (
                    .fix₁ (
                      .lam { 102 ⇛
                      .lam { 103 ⇛
                        .ifz₁ n (
                          .lift (.lit 1)) (
                          .binary₂ .mul (.code x₀) (.app₁ f (.binary₁ .sub n (.lit 1))))}}))) (
                  .bvar 0))) (
              .binary₁ .sub n (.lit 1))))}) (
      .lit 2)}

def expr₈ : Expr :=
  .lam𝕔 { 0 ⇛
    .ifz₁ (.lit 2) (
      .lift (.lit 1)) (
      .binary₂ .mul (
        .code x₀) (
        .app₁ (
          .lam (
            .app₁ (
              .app₁ (
                .lam { 102 ⇛
                .lam { 103 ⇛
                  .ifz₁ n (
                    .lift (.lit 1)) (
                    .binary₂ .mul (.code x₀) (.app₁ f (.binary₁ .sub n (.lit 1))))}}) (
                .fix₁ (
                  .lam { 102 ⇛
                  .lam { 103 ⇛
                    .ifz₁ n (
                      .lift (.lit 1)) (
                      .binary₂ .mul (.code x₀) (.app₁ f (.binary₁ .sub n (.lit 1))))}}))) (
              .bvar 0))) (
          .binary₁ .sub (.lit 2) (.lit 1))))}

def expr₉ : Expr :=
  .lam𝕔 { 0 ⇛
    .binary₂ .mul (
      .code x₀) (
      .app₁ (
        .lam (
          .app₁ (
            .app₁ (
              .lam { 102 ⇛
              .lam { 103 ⇛
                .ifz₁ n (
                  .lift (.lit 1)) (
                  .binary₂ .mul (.code x₀) (.app₁ f (.binary₁ .sub n (.lit 1))))}}) (
              .fix₁ (
                .lam { 102 ⇛
                .lam { 103 ⇛
                  .ifz₁ n (
                    .lift (.lit 1)) (
                    .binary₂ .mul (.code x₀) (.app₁ f (.binary₁ .sub n (.lit 1))))}}))) (
            .bvar 0))) (
        .binary₁ .sub (.lit 2) (.lit 1)))}

def expr𝕩₀ : Expr :=
  .lam𝕔 { 0 ⇛
    .binary₂ .mul (
      .code x₀) (
      .app₁ (
        .lam (
          .app₁ (
            .app₁ (
              .lam { 102 ⇛
              .lam { 103 ⇛
                .ifz₁ n (
                  .lift (.lit 1)) (
                  .binary₂ .mul (.code x₀) (.app₁ f (.binary₁ .sub n (.lit 1))))}}) (
              .fix₁ (
                .lam { 102 ⇛
                .lam { 103 ⇛
                  .ifz₁ n (
                    .lift (.lit 1)) (
                    .binary₂ .mul (.code x₀) (.app₁ f (.binary₁ .sub n (.lit 1))))}}))) (
            .bvar 0))) (
        .lit 1))}

def expr𝕩₁ : Expr :=
  .lam𝕔 { 0 ⇛
    .binary₂ .mul (
      .code x₀) (
      .app₁ (
        .app₁ (
          .lam { 102 ⇛
          .lam { 103 ⇛
            .ifz₁ n (
              .lift (.lit 1)) (
              .binary₂ .mul (.code x₀) (.app₁ f (.binary₁ .sub n (.lit 1))))}}) (
          .fix₁ (
            .lam { 102 ⇛
            .lam { 103 ⇛
              .ifz₁ n (
                .lift (.lit 1)) (
                .binary₂ .mul (.code x₀) (.app₁ f (.binary₁ .sub n (.lit 1))))}}))) (
        .lit 1))}

def expr𝕩₂ : Expr :=
  .lam𝕔 { 0 ⇛
    .binary₂ .mul (
      .code x₀) (
      .app₁ (
        .app₁ (
          .lam { 102 ⇛
          .lam { 103 ⇛
            .ifz₁ n (
              .lift (.lit 1)) (
              .binary₂ .mul (.code x₀) (.app₁ f (.binary₁ .sub n (.lit 1))))}}) (
          .lam (
            .app₁ (
              .app₁ (
                .lam { 102 ⇛
                .lam { 103 ⇛
                  .ifz₁ n (
                    .lift (.lit 1)) (
                    .binary₂ .mul (.code x₀) (.app₁ f (.binary₁ .sub n (.lit 1))))}}) (
                .fix₁ (
                  .lam { 102 ⇛
                  .lam { 103 ⇛
                    .ifz₁ n (
                      .lift (.lit 1)) (
                      .binary₂ .mul (.code x₀) (.app₁ f (.binary₁ .sub n (.lit 1))))}}))) (
              .bvar 0)))) (
        .lit 1))}

def expr𝕩₃ : Expr :=
  .lam𝕔 { 0 ⇛
    .binary₂ .mul (
      .code x₀) (
      .app₁ (
        .lam { 103 ⇛
          .ifz₁ n (
            .lift (.lit 1)) (
            .binary₂ .mul (
              .code x₀) (
              .app₁ (
                .lam (
                  .app₁ (
                    .app₁ (
                      .lam { 102 ⇛
                      .lam { 103 ⇛
                        .ifz₁ n (
                          .lift (.lit 1)) (
                          .binary₂ .mul (.code x₀) (.app₁ f (.binary₁ .sub n (.lit 1))))}}) (
                      .fix₁ (
                        .lam { 102 ⇛
                        .lam { 103 ⇛
                          .ifz₁ n (
                            .lift (.lit 1)) (
                            .binary₂ .mul (.code x₀) (.app₁ f (.binary₁ .sub n (.lit 1))))}}))) (
                    .bvar 0))) (
                .binary₁ .sub n (.lit 1))))}) (
        .lit 1))}

def expr𝕩₄ : Expr :=
  .lam𝕔 { 0 ⇛
    .binary₂ .mul (
      .code x₀) (
      .ifz₁ (.lit 1) (
        .lift (.lit 1)) (
        .binary₂ .mul (
          .code x₀) (
          .app₁ (
            .lam (
              .app₁ (
                .app₁ (
                  .lam { 102 ⇛
                  .lam { 103 ⇛
                    .ifz₁ n (
                      .lift (.lit 1)) (
                      .binary₂ .mul (.code x₀) (.app₁ f (.binary₁ .sub n (.lit 1))))}}) (
                  .fix₁ (
                    .lam { 102 ⇛
                    .lam { 103 ⇛
                      .ifz₁ n (
                        .lift (.lit 1)) (
                        .binary₂ .mul (.code x₀) (.app₁ f (.binary₁ .sub n (.lit 1))))}}))) (
                .bvar 0))) (
            .binary₁ .sub (.lit 1) (.lit 1)))))}

def expr𝕩₅ : Expr :=
  .lam𝕔 { 0 ⇛
    .binary₂ .mul (
      .code x₀) (
      .binary₂ .mul (
        .code x₀) (
        .app₁ (
          .lam (
            .app₁ (
              .app₁ (
                .lam { 102 ⇛
                .lam { 103 ⇛
                  .ifz₁ n (
                    .lift (.lit 1)) (
                    .binary₂ .mul (.code x₀) (.app₁ f (.binary₁ .sub n (.lit 1))))}}) (
                .fix₁ (
                  .lam { 102 ⇛
                  .lam { 103 ⇛
                    .ifz₁ n (
                      .lift (.lit 1)) (
                      .binary₂ .mul (.code x₀) (.app₁ f (.binary₁ .sub n (.lit 1))))}}))) (
              .bvar 0))) (
          .binary₁ .sub (.lit 1) (.lit 1))))}

def expr𝕩₆ : Expr :=
  .lam𝕔 { 0 ⇛
    .binary₂ .mul (
      .code x₀) (
      .binary₂ .mul (
        .code x₀) (
        .app₁ (
          .lam (
            .app₁ (
              .app₁ (
                .lam { 102 ⇛
                .lam { 103 ⇛
                  .ifz₁ n (
                    .lift (.lit 1)) (
                    .binary₂ .mul (.code x₀) (.app₁ f (.binary₁ .sub n (.lit 1))))}}) (
                .fix₁ (
                  .lam { 102 ⇛
                  .lam { 103 ⇛
                    .ifz₁ n (
                      .lift (.lit 1)) (
                      .binary₂ .mul (.code x₀) (.app₁ f (.binary₁ .sub n (.lit 1))))}}))) (
              .bvar 0))) (
          .lit 0)))}

def expr𝕩₇ : Expr :=
  .lam𝕔 { 0 ⇛
    .binary₂ .mul (
      .code x₀) (
      .binary₂ .mul (
        .code x₀) (
        .app₁ (
          .app₁ (
            .lam { 102 ⇛
            .lam { 103 ⇛
              .ifz₁ n (
                .lift (.lit 1)) (
                .binary₂ .mul (.code x₀) (.app₁ f (.binary₁ .sub n (.lit 1))))}}) (
            .fix₁ (
              .lam { 102 ⇛
              .lam { 103 ⇛
                .ifz₁ n (
                  .lift (.lit 1)) (
                  .binary₂ .mul (.code x₀) (.app₁ f (.binary₁ .sub n (.lit 1))))}}))) (
          .lit 0)))}

def expr𝕩₈ : Expr :=
  .lam𝕔 { 0 ⇛
    .binary₂ .mul (
      .code x₀) (
      .binary₂ .mul (
        .code x₀) (
        .app₁ (
          .app₁ (
            .lam { 102 ⇛
            .lam { 103 ⇛
              .ifz₁ n (
                .lift (.lit 1)) (
                .binary₂ .mul (.code x₀) (.app₁ f (.binary₁ .sub n (.lit 1))))}}) (
            .lam (
              .app₁ (
                .app₁ (
                  .lam { 102 ⇛
                  .lam { 103 ⇛
                    .ifz₁ n (
                      .lift (.lit 1)) (
                      .binary₂ .mul (.code x₀) (.app₁ f (.binary₁ .sub n (.lit 1))))}}) (
                  .fix₁ (
                    .lam { 102 ⇛
                    .lam { 103 ⇛
                      .ifz₁ n (
                        .lift (.lit 1)) (
                        .binary₂ .mul (.code x₀) (.app₁ f (.binary₁ .sub n (.lit 1))))}}))) (
                .bvar 0)))) (
          .lit 0)))}

def expr𝕩₉ : Expr :=
  .lam𝕔 { 0 ⇛
    .binary₂ .mul (
      .code x₀) (
      .binary₂ .mul (
        .code x₀) (
        .app₁ (
          .lam { 103 ⇛
            .ifz₁ n (
              .lift (.lit 1)) (
              .binary₂ .mul (
                .code x₀) (
                .app₁ (
                  .lam (
                    .app₁ (
                      .app₁ (
                        .lam { 102 ⇛
                        .lam { 103 ⇛
                          .ifz₁ n (
                            .lift (.lit 1)) (
                            .binary₂ .mul (.code x₀) (.app₁ f (.binary₁ .sub n (.lit 1))))}}) (
                        .fix₁ (
                          .lam { 102 ⇛
                          .lam { 103 ⇛
                            .ifz₁ n (
                              .lift (.lit 1)) (
                              .binary₂ .mul (.code x₀) (.app₁ f (.binary₁ .sub n (.lit 1))))}}))) (
                      .bvar 0))) (
                  .binary₁ .sub n (.lit 1))))}) (
          .lit 0)))}

def expr𝕩𝕩₀ : Expr :=
  .lam𝕔 { 0 ⇛
    .binary₂ .mul (
      .code x₀) (
      .binary₂ .mul (
        .code x₀) (
        .ifz₁ (.lit 0) (
          .lift (.lit 1)) (
          .binary₂ .mul (
            .code x₀) (
            .app₁ (
              .lam (
                .app₁ (
                  .app₁ (
                    .lam { 102 ⇛
                    .lam { 103 ⇛
                      .ifz₁ n (
                        .lift (.lit 1)) (
                        .binary₂ .mul (.code x₀) (.app₁ f (.binary₁ .sub n (.lit 1))))}}) (
                    .fix₁ (
                      .lam { 102 ⇛
                      .lam { 103 ⇛
                        .ifz₁ n (
                          .lift (.lit 1)) (
                          .binary₂ .mul (.code x₀) (.app₁ f (.binary₁ .sub n (.lit 1))))}}))) (
                  .bvar 0))) (
              .binary₁ .sub (.lit 0) (.lit 1))))))}

def expr𝕩𝕩₁ : Expr :=
  .lam𝕔 { 0 ⇛
    .binary₂ .mul (
      .code x₀) (
      .binary₂ .mul (
        .code x₀) (
        .lift (.lit 1)))}

def expr𝕩𝕩₂ : Expr :=
  .lam𝕔 { 0 ⇛
    .binary₂ .mul (
      .code x₀) (
      .binary₂ .mul (
        .code x₀) (
        .reflect (.lit 1)))}

def expr𝕩𝕩₃ : Expr :=
  .lam𝕔 { 0 ⇛
    .lets𝕔 (.lit 1) { 1 ⇛
    .binary₂ .mul (
      .code x₀) (
      .binary₂ .mul (
        .code x₀) (
        .code x₁))}}

def expr𝕩𝕩₄ : Expr :=
  .lam𝕔 { 0 ⇛
    .lets𝕔 (.lit 1) { 1 ⇛
    .binary₂ .mul (
      .code x₀) (
      .reflect (.binary₁ .mul x₀ x₁))}}

def expr𝕩𝕩₅ : Expr :=
  .lam𝕔 { 0 ⇛
    .lets𝕔 (.lit 1) { 1 ⇛
    .lets𝕔 (.binary₁ .mul x₀ x₁) { 2 ⇛
    .binary₂ .mul (
      .code x₀) (
      .code x₂)}}}

def expr𝕩𝕩₆ : Expr :=
  .lam𝕔 { 0 ⇛
    .lets𝕔 (.lit 1) { 1 ⇛
    .lets𝕔 (.binary₁ .mul x₀ x₁) { 2 ⇛
    .reflect (.binary₁ .mul x₀ x₂)}}}

def expr𝕩𝕩₇ : Expr :=
  .lam𝕔 { 0 ⇛
    .lets𝕔 (.lit 1) { 1 ⇛
    .lets𝕔 (.binary₁ .mul x₀ x₁) { 2 ⇛
    .lets𝕔 (.binary₁ .mul x₀ x₂) { 3 ⇛
    .code x₃}}}}

def expr𝕩𝕩₈ : Expr :=
  .lam𝕔 { 0 ⇛
    .lets𝕔 (.lit 1) { 1 ⇛
    .lets𝕔 (.binary₁ .mul x₀ x₁) { 2 ⇛
    .code (
      .lets (.binary₁ .mul x₀ x₂) { 3 ⇛
      x₃})}}}

def expr𝕩𝕩₉ : Expr :=
  .lam𝕔 { 0 ⇛
    .lets𝕔 (.lit 1) { 1 ⇛
    .code (
      .lets (.binary₁ .mul x₀ x₁) { 2 ⇛
      .lets (.binary₁ .mul x₀ x₂) { 3 ⇛
      x₃}})}}

def expr𝕩𝕩𝕩₀ : Expr :=
  .lam𝕔 { 0 ⇛
    .code (
      .lets (.lit 1) { 1 ⇛
      .lets (.binary₁ .mul x₀ x₁) { 2 ⇛
      .lets (.binary₁ .mul x₀ x₂) { 3 ⇛
      x₃}}})}

def expr𝕩𝕩𝕩₁ : Expr :=
  .reflect (
    .lam { 0 ⇛
      .lets (.lit 1) { 1 ⇛
      .lets (.binary₁ .mul x₀ x₁) { 2 ⇛
      .lets (.binary₁ .mul x₀ x₂) { 3 ⇛
      x₃}}}})

def expr𝕩𝕩𝕩₂ : Expr :=
  .lets𝕔 (
    .lam { 0 ⇛
      .lets (.lit 1) { 1 ⇛
      .lets (.binary₁ .mul x₀ x₁) { 2 ⇛
      .lets (.binary₁ .mul x₀ x₂) { 3 ⇛
      x₃}}}}) { 4 ⇛
  .code x₄}

def expr𝕩𝕩𝕩₃ : Expr :=
  .code (
    .lets (
      .lam { 0 ⇛
        .lets (.lit 1) { 1 ⇛
        .lets (.binary₁ .mul x₀ x₁) { 2 ⇛
        .lets (.binary₁ .mul x₀ x₂) { 3 ⇛
        x₃}}}}) { 4 ⇛
    x₄})

example : (⟨ϵ, expr₀⟩ ⭢ ⟨ϵ, expr₁⟩) := by
  apply step_lvl.pure id
  repeat constructor

example : (⟨ϵ, expr₁⟩ ⭢ ⟨ϵ, expr₂⟩) := by
  apply step_lvl.pure id
  repeat constructor

example : (⟨ϵ, expr₂⟩ ⭢ ⟨ϵ, expr₃⟩) := by
  apply step_lvl.pure (fun X => .lam𝕔 {0 ↤ 0} .app₁ X _)
  apply ctx𝕄.consℝ (fun X => .lam𝕔 {0 ↤ 0} X); repeat constructor
  apply ctx𝕄.cons𝔹 (fun X => .app₁ X _)
  repeat constructor

example : (⟨ϵ, expr₃⟩ ⭢ ⟨ϵ, expr₄⟩) := by
  apply step_lvl.pure (fun X => .lam𝕔 {0 ↤ 0} .app₁ X _)
  apply ctx𝕄.consℝ (fun X => .lam𝕔 {0 ↤ 0} X)
  apply ctxℝ.lam𝕔
  apply ctx𝕄.cons𝔹 (fun X => .app₁ X _)
  repeat constructor

example : (⟨ϵ, expr₄⟩ ⭢ ⟨ϵ, expr₅⟩) := by
  apply step_lvl.pure (fun X => .lam𝕔 {0 ↤ 0} X)
  apply ctx𝕄.consℝ (fun X => .lam𝕔 {0 ↤ 0} X)
  repeat constructor

example : (⟨ϵ, expr₅⟩ ⭢ ⟨ϵ, expr₆⟩) := by
  let left : Expr :=
    .lam { 102 ⇛
          .lam { 103 ⇛
            .ifz₁ n (
              .lift (.lit 1)) (
              .binary₂ .mul (.code x₀) (.app₁ f (.binary₁ .sub n (.lit 1))))}}
  apply step_lvl.pure (fun X => .lam𝕔 {0 ↤ 0} .app₁ (.app₁ left X) _)
  apply ctx𝕄.consℝ (fun X => .lam𝕔 {0 ↤ 0} X); repeat constructor
  apply ctx𝕄.cons𝔹 (fun X => .app₁ X _)
  repeat constructor

example : (⟨ϵ, expr₆⟩ ⭢ ⟨ϵ, expr₇⟩) := by
  apply step_lvl.pure (fun X => .lam𝕔 {0 ↤ 0} .app₁ X _)
  apply ctx𝕄.consℝ (fun X => .lam𝕔 {0 ↤ 0} X); repeat constructor
  apply ctx𝕄.cons𝔹 (fun X => .app₁ X _)
  repeat constructor

example : (⟨ϵ, expr₇⟩ ⭢ ⟨ϵ, expr₈⟩) := by
  apply step_lvl.pure (fun X => .lam𝕔 {0 ↤ 0} X)
  apply ctx𝕄.consℝ (fun X => .lam𝕔 {0 ↤ 0} X)
  repeat constructor

example : (⟨ϵ, expr₈⟩ ⭢ ⟨ϵ, expr₉⟩) := by
  apply step_lvl.pure (fun X => .lam𝕔 {0 ↤ 0} X)
  apply ctx𝕄.consℝ (fun X => .lam𝕔 {0 ↤ 0} X)
  repeat constructor

example : (⟨ϵ, expr₉⟩ ⭢ ⟨ϵ, expr𝕩₀⟩) := by
  let left : Expr :=
    .lam (
      .app₁ (
        .app₁ (
          .lam { 102 ⇛
          .lam { 103 ⇛
            .ifz₁ n (
              .lift (.lit 1)) (
              .binary₂ .mul (.code x₀) (.app₁ f (.binary₁ .sub n (.lit 1))))}}) (
          .fix₁ (
            .lam { 102 ⇛
            .lam { 103 ⇛
              .ifz₁ n (
                .lift (.lit 1)) (
                .binary₂ .mul (.code x₀) (.app₁ f (.binary₁ .sub n (.lit 1))))}}))) (
        .bvar 0))
  apply step_lvl.pure (fun X => .lam𝕔 {0 ↤ 0} .binary₂ .mul (.code x₀) (.app₁ left X))
  apply ctx𝕄.consℝ (fun X => .lam𝕔 {0 ↤ 0} X)
  repeat constructor

example : (⟨ϵ, expr𝕩₀⟩ ⭢ ⟨ϵ, expr𝕩₁⟩) := by
  apply step_lvl.pure (fun X => .lam𝕔 {0 ↤ 0} .binary₂ .mul (.code x₀) X)
  apply ctx𝕄.consℝ (fun X => .lam𝕔 {0 ↤ 0} X)
  repeat constructor

example : (⟨ϵ, expr𝕩₁⟩ ⭢ ⟨ϵ, expr𝕩₂⟩) := by
  let left : Expr :=
    .lam { 102 ⇛
          .lam { 103 ⇛
            .ifz₁ n (
              .lift (.lit 1)) (
              .binary₂ .mul (.code x₀) (.app₁ f (.binary₁ .sub n (.lit 1))))}}
  apply step_lvl.pure (fun X => .lam𝕔 {0 ↤ 0} .binary₂ .mul (.code x₀) (.app₁ (.app₁ left X) _))
  apply ctx𝕄.consℝ (fun X => .lam𝕔 {0 ↤ 0} X); repeat constructor
  apply ctx𝕄.cons𝔹 (fun X => .app₁ X _)
  repeat constructor

example : (⟨ϵ, expr𝕩₂⟩ ⭢ ⟨ϵ, expr𝕩₃⟩) := by
  apply step_lvl.pure (fun X => .lam𝕔 {0 ↤ 0} .binary₂ .mul (.code x₀) (.app₁ X _))
  apply ctx𝕄.consℝ (fun X => .lam𝕔 {0 ↤ 0} X); repeat constructor
  apply ctx𝕄.cons𝔹 (fun X => .app₁ X _)
  repeat constructor

example : (⟨ϵ, expr𝕩₃⟩ ⭢ ⟨ϵ, expr𝕩₄⟩) := by
  apply step_lvl.pure (fun X => .lam𝕔 {0 ↤ 0} .binary₂ .mul (.code x₀) X)
  apply ctx𝕄.consℝ (fun X => .lam𝕔 {0 ↤ 0} X)
  repeat constructor

example : (⟨ϵ, expr𝕩₄⟩ ⭢ ⟨ϵ, expr𝕩₅⟩) := by
  apply step_lvl.pure (fun X => .lam𝕔 {0 ↤ 0} .binary₂ .mul (.code x₀) X)
  apply ctx𝕄.consℝ (fun X => .lam𝕔 {0 ↤ 0} X)
  repeat constructor

example : (⟨ϵ, expr𝕩₅⟩ ⭢ ⟨ϵ, expr𝕩₆⟩) := by
  let left : Expr :=
    .lam (
      .app₁ (
        .app₁ (
          .lam { 102 ⇛
          .lam { 103 ⇛
            .ifz₁ n (
              .lift (.lit 1)) (
              .binary₂ .mul (.code x₀) (.app₁ f (.binary₁ .sub n (.lit 1))))}}) (
          .fix₁ (
            .lam { 102 ⇛
            .lam { 103 ⇛
              .ifz₁ n (
                .lift (.lit 1)) (
                .binary₂ .mul (.code x₀) (.app₁ f (.binary₁ .sub n (.lit 1))))}}))) (
        .bvar 0))
  apply step_lvl.pure (fun X => .lam𝕔 {0 ↤ 0} .binary₂ .mul (.code x₀) (.binary₂ .mul (.code x₀) (.app₁ left X)))
  apply ctx𝕄.consℝ (fun X => .lam𝕔 {0 ↤ 0} X)
  repeat constructor

example : (⟨ϵ, expr𝕩₆⟩ ⭢ ⟨ϵ, expr𝕩₇⟩) := by
  apply step_lvl.pure (fun X => .lam𝕔 {0 ↤ 0} .binary₂ .mul (.code x₀) (.binary₂ .mul (.code x₀) X))
  apply ctx𝕄.consℝ (fun X => .lam𝕔 {0 ↤ 0} X)
  repeat constructor

example : (⟨ϵ, expr𝕩₇⟩ ⭢ ⟨ϵ, expr𝕩₈⟩) := by
  let left : Expr :=
    .lam { 102 ⇛
          .lam { 103 ⇛
            .ifz₁ n (
              .lift (.lit 1)) (
              .binary₂ .mul (.code x₀) (.app₁ f (.binary₁ .sub n (.lit 1))))}}
  apply step_lvl.pure (fun X => .lam𝕔 ({0 ↤ 0} .binary₂ .mul (.code x₀) (.binary₂ .mul (.code x₀) (.app₁ (.app₁ left X) _))))
  apply ctx𝕄.consℝ (fun X => .lam𝕔 {0 ↤ 0} X); repeat constructor
  apply ctx𝕄.cons𝔹 (fun X => .app₁ X _)
  repeat constructor

example : (⟨ϵ, expr𝕩₈⟩ ⭢ ⟨ϵ, expr𝕩₉⟩) := by
  apply step_lvl.pure (fun X => .lam𝕔 ({0 ↤ 0} .binary₂ .mul (.code x₀) (.binary₂ .mul (.code x₀) (.app₁ X _))))
  apply ctx𝕄.consℝ (fun X => .lam𝕔 ({0 ↤ 0} X)); repeat constructor
  apply ctx𝕄.cons𝔹 (fun X => .app₁ X _)
  repeat constructor

example : (⟨ϵ, expr𝕩₉⟩ ⭢ ⟨ϵ, expr𝕩𝕩₀⟩) := by
  apply step_lvl.pure (fun X => .lam𝕔 {0 ↤ 0} .binary₂ .mul (.code x₀) (.binary₂ .mul (.code x₀) X))
  apply ctx𝕄.consℝ (fun X => .lam𝕔 {0 ↤ 0} X)
  repeat constructor

example : (⟨ϵ, expr𝕩𝕩₀⟩ ⭢ ⟨ϵ, expr𝕩𝕩₁⟩) := by
  apply step_lvl.pure (fun X => .lam𝕔 {0 ↤ 0} .binary₂ .mul (.code x₀) (.binary₂ .mul (.code x₀) X))
  apply ctx𝕄.consℝ (fun X => .lam𝕔 {0 ↤ 0} X)
  repeat constructor

example : (⟨ϵ, expr𝕩𝕩₁⟩ ⭢ ⟨ϵ, expr𝕩𝕩₂⟩) := by
  apply step_lvl.pure (fun X => .lam𝕔 {0 ↤ 0} .binary₂ .mul (.code x₀) (.binary₂ .mul (.code x₀) X))
  apply ctx𝕄.consℝ (fun X => .lam𝕔 {0 ↤ 0} X)
  repeat constructor

example : (⟨ϵ, expr𝕩𝕩₂⟩ ⭢ ⟨ϵ, expr𝕩𝕩₃⟩) := by
  apply step_lvl.reflect
    (fun X => .lam𝕔 {0 ↤ 0} X)
    (fun X =>
      .binary₂ .mul (
        .code x₀) (
        .binary₂ .mul (
          .code x₀) (
          X)))
  repeat constructor

example : (⟨ϵ, expr𝕩𝕩₃⟩ ⭢ ⟨ϵ, expr𝕩𝕩₄⟩) := by
  apply step_lvl.pure
    (fun X =>
      .lam𝕔 { 0 ⇛
        .lets𝕔 (.lit 1) { 1 ⇛
        .binary₂ .mul (
          .code x₀) (
          X)}})
  apply ctx𝕄.consℝ (fun X => .lam𝕔 {0 ↤ 0} X)
  apply ctxℝ.lam𝕔
  apply ctx𝕄.consℝ (fun X => .lets𝕔 (.lit 1) {0 ↤ 1} X)
  repeat constructor

example : (⟨ϵ, expr𝕩𝕩₄⟩ ⭢ ⟨ϵ, expr𝕩𝕩₅⟩) := by
  apply step_lvl.reflect
    (fun X => .lam𝕔 ({0 ↤ 0} .lets𝕔 (.lit 1) {0 ↤ 1} X))
    (fun X => .binary₂ .mul (.code x₀) X)
  apply ctxℙ.consℚ (fun X => .lam𝕔 {0 ↤ 0} .lets𝕔 (.lit 1) {0 ↤ 1} X)
  apply ctxℚ.consℝ (fun X => .lam𝕔 ({0 ↤ 0} X))
  repeat constructor

example : (⟨ϵ, expr𝕩𝕩₅⟩ ⭢ ⟨ϵ, expr𝕩𝕩₆⟩) := by
  apply step_lvl.pure
    (fun X =>
      .lam𝕔 { 0 ⇛
        .lets𝕔 (.lit 1) { 1 ⇛
        .lets𝕔 (.binary₁ .mul x₀ x₁) { 2 ⇛
        X}}})
  apply ctx𝕄.consℝ (fun X => .lam𝕔 {0 ↤ 0} X)
  apply ctxℝ.lam𝕔
  apply ctx𝕄.consℝ (fun X => .lets𝕔 (.lit 1) {0 ↤ 1} X)
  apply ctxℝ.lets𝕔; constructor
  apply ctx𝕄.consℝ (fun X => .lets𝕔 (.binary₁ .mul x₀ x₁) {0 ↤ 2} X)
  repeat constructor

example : (⟨ϵ, expr𝕩𝕩₆⟩ ⭢ ⟨ϵ, expr𝕩𝕩₇⟩) := by
  apply step_lvl.reflect
    (fun X =>
      .lam𝕔 { 0 ⇛
        .lets𝕔 (.lit 1) { 1 ⇛
        .lets𝕔 (.binary₁ .mul x₀ x₁) { 2 ⇛
        X}}})
    id
  apply ctxℙ.consℚ
    (fun X =>
      .lam𝕔 { 0 ⇛
        .lets𝕔 (.lit 1) { 1 ⇛
        .lets𝕔 (.binary₁ .mul x₀ x₁) { 2 ⇛
        X}}})
  apply ctxℚ.consℝ (fun X => .lam𝕔 {0 ↤ 0} X)
  apply ctxℝ.lam𝕔
  apply ctxℚ.consℝ (fun X => .lets𝕔 (.lit 1) {0 ↤ 1} X)
  repeat constructor

example : (⟨ϵ, expr𝕩𝕩₇⟩ ⭢ ⟨ϵ, expr𝕩𝕩₈⟩) := by
  apply step_lvl.pure
    (fun X =>
      .lam𝕔 { 0 ⇛
        .lets𝕔 (.lit 1) { 1 ⇛
        .lets𝕔 (.binary₁ .mul x₀ x₁) { 2 ⇛
        X}}})
  apply ctx𝕄.consℝ (fun X => .lam𝕔 {0 ↤ 0} X)
  apply ctxℝ.lam𝕔
  apply ctx𝕄.consℝ (fun X => .lets𝕔 (.lit 1) {0 ↤ 1} X)
  apply ctxℝ.lets𝕔; constructor
  apply ctx𝕄.consℝ (fun X => .lets𝕔 (.binary₁ .mul x₀ x₁) {0 ↤ 2} X)
  repeat constructor

example : (⟨ϵ, expr𝕩𝕩₈⟩ ⭢ ⟨ϵ, expr𝕩𝕩₉⟩) := by
  apply step_lvl.pure
    (fun X =>
      .lam𝕔 { 0 ⇛
        .lets𝕔 (.lit 1) { 1 ⇛
        X}})
  apply ctx𝕄.consℝ (fun X => .lam𝕔 {0 ↤ 0} X)
  apply ctxℝ.lam𝕔
  apply ctx𝕄.consℝ (fun X => .lets𝕔 (.lit 1) {0 ↤ 1} X)
  repeat constructor

example : (⟨ϵ, expr𝕩𝕩₉⟩ ⭢ ⟨ϵ, expr𝕩𝕩𝕩₀⟩) := by
  apply step_lvl.pure
    (fun X =>
      .lam𝕔 { 0 ⇛
        X})
  apply ctx𝕄.consℝ (fun X => .lam𝕔 {0 ↤ 0} X)
  apply ctxℝ.lam𝕔
  repeat constructor

example : (⟨ϵ, expr𝕩𝕩𝕩₀⟩ ⭢ ⟨ϵ, expr𝕩𝕩𝕩₁⟩) := by
  apply step_lvl.pure id
  repeat constructor

example : (⟨ϵ, expr𝕩𝕩𝕩₁⟩ ⭢ ⟨ϵ, expr𝕩𝕩𝕩₂⟩) := by
  apply step_lvl.reflect id id
  repeat constructor

example : (⟨ϵ, expr𝕩𝕩𝕩₂⟩ ⭢ ⟨ϵ, expr𝕩𝕩𝕩₃⟩) := by
  apply step_lvl.pure id
  repeat constructor

example : typing_reification ⦰ expr₀ (.rep (.arrow .nat .nat ⊥)) ⊤ :=
  by
  apply typing_reification.reify; rw [← Effect.pure_union ⊤]
  apply typing.lets
  apply typing.lam
  apply typing.fix₁
  . rw [Effect.reify_union ⊥]
  apply typing.lam
  apply typing.lam _ _ _ _ _ ⊤; rw [← Effect.union_reify (⊥ ∪ ⊤)]
  apply typing.ifz₁
  . repeat constructor
  . apply typing.lift_lit; apply typing.lit
  . repeat constructor
  repeat constructor

example : typing_reification ⦰ expr𝕩𝕩𝕩₃ (.rep (.arrow .nat .nat ⊥)) ⊥ :=
  by
  repeat
    first
    | constructor
    | rw [← Effect.union_pure ⊥]

end StagePower

-- mutable stage power function xⁿ
namespace MutableStagePower

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
--
-- -->*
--
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
  .lets (.alloc₂ (.lift (.lit 1))) { 100 ⇛
  .lets (
    .lam { 102 ⇛
      .fix₁ (
        .lam { 103 ⇛
        .lam { 104 ⇛
          .ifz₁ n (
            .load₂ ref) (
            .lets (.store₂ ref (.binary₂ .mul x (.load₂ ref))) (
            .app₁ f (.binary₁ .sub n (.lit 1))))}})}) { 101 ⇛
  .lift (
    .lam { 105 ⇛
      .app₁ (.app₁ power y) (.lit 2)})}}

def expr₁ : Expr :=
  .lets (.alloc₂ (.reflect (.lit 1))) { 100 ⇛
  .lets (
    .lam { 102 ⇛
      .fix₁ (
        .lam { 103 ⇛
        .lam { 104 ⇛
          .ifz₁ n (
            .load₂ ref) (
            .lets (.store₂ ref (.binary₂ .mul x (.load₂ ref))) (
            .app₁ f (.binary₁ .sub n (.lit 1))))}})}) { 101 ⇛
  .lift (
    .lam { 105 ⇛
      .app₁ (.app₁ power y) (.lit 2)})}}

def expr₂ : Expr :=
  .lets𝕔 (.lit 1) { 0 ⇛
  .lets (.alloc₂ (.code x₀)) { 100 ⇛
  .lets (
    .lam { 102 ⇛
      .fix₁ (
        .lam { 103 ⇛
        .lam { 104 ⇛
          .ifz₁ n (
            .load₂ ref) (
            .lets (.store₂ ref (.binary₂ .mul x (.load₂ ref))) (
            .app₁ f (.binary₁ .sub n (.lit 1))))}})}) { 101 ⇛
  .lift (
    .lam { 105 ⇛
      .app₁ (.app₁ power y) (.lit 2)})}}}

def expr₃ : Expr :=
  .lets𝕔 (.lit 1) { 0 ⇛
  .lets (.reflect (.alloc₁ x₀)) { 100 ⇛
  .lets (
    .lam { 102 ⇛
      .fix₁ (
        .lam { 103 ⇛
        .lam { 104 ⇛
          .ifz₁ n (
            .load₂ ref) (
            .lets (.store₂ ref (.binary₂ .mul x (.load₂ ref))) (
            .app₁ f (.binary₁ .sub n (.lit 1))))}})}) { 101 ⇛
  .lift (
    .lam { 105 ⇛
      .app₁ (.app₁ power y) (.lit 2)})}}}

def expr₄ : Expr :=
  .lets𝕔 (.lit 1) { 0 ⇛
  .lets𝕔 (.alloc₁ x₀) { 1 ⇛
  .lets (.code x₁) { 100 ⇛
  .lets (
    .lam { 102 ⇛
      .fix₁ (
        .lam { 103 ⇛
        .lam { 104 ⇛
          .ifz₁ n (
            .load₂ ref) (
            .lets (.store₂ ref (.binary₂ .mul x (.load₂ ref))) (
            .app₁ f (.binary₁ .sub n (.lit 1))))}})}) { 101 ⇛
  .lift (
    .lam { 105 ⇛
      .app₁ (.app₁ power y) (.lit 2)})}}}}

def expr₅ : Expr :=
  .lets𝕔 (.lit 1) { 0 ⇛
  .lets𝕔 (.alloc₁ x₀) { 1 ⇛
  .lets (
    .lam { 102 ⇛
      .fix₁ (
        .lam { 103 ⇛
        .lam { 104 ⇛
          .ifz₁ n (
            .load₂ (.code x₁)) (
            .lets (.store₂ (.code x₁) (.binary₂ .mul x (.load₂ (.code x₁)))) (
            .app₁ f (.binary₁ .sub n (.lit 1))))}})}) { 101 ⇛
  .lift (
    .lam { 105 ⇛
      .app₁ (.app₁ power y) (.lit 2)})}}}

def expr₆ : Expr :=
  .lets𝕔 (.lit 1) { 0 ⇛
  .lets𝕔 (.alloc₁ x₀) { 1 ⇛
  .lift (
    .lam { 105 ⇛
      .app₁ (
        .app₁ (
          .lam { 102 ⇛
            .fix₁ (
              .lam { 103 ⇛
              .lam { 104 ⇛
                .ifz₁ n (
                  .load₂ (.code x₁)) (
                  .lets (.store₂ (.code x₁) (.binary₂ .mul x (.load₂ (.code x₁)))) (
                  .app₁ f (.binary₁ .sub n (.lit 1))))}})})
          y) (
        .lit 2)})}}

def expr₇ : Expr :=
  .lets𝕔 (.lit 1) { 0 ⇛
  .lets𝕔 (.alloc₁ x₀) { 1 ⇛
  .lam𝕔 { 2 ⇛
    .app₁ (
      .app₁ (
        .lam { 102 ⇛
          .fix₁ (
            .lam { 103 ⇛
            .lam { 104 ⇛
              .ifz₁ n (
                .load₂ (.code x₁)) (
                .lets (.store₂ (.code x₁) (.binary₂ .mul x (.load₂ (.code x₁)))) (
                .app₁ f (.binary₁ .sub n (.lit 1))))}})}) (
        .code x₂)) (
      .lit 2)}}}

def expr₈ : Expr :=
  .lets𝕔 (.lit 1) { 0 ⇛
  .lets𝕔 (.alloc₁ x₀) { 1 ⇛
  .lam𝕔 { 2 ⇛
    .app₁ (
      .fix₁ (
        .lam { 103 ⇛
        .lam { 104 ⇛
          .ifz₁ n (
            .load₂ (.code x₁)) (
            .lets (.store₂ (.code x₁) (.binary₂ .mul (.code x₂) (.load₂ (.code x₁)))) (
            .app₁ f (.binary₁ .sub n (.lit 1))))}})) (
      .lit 2)}}}

def expr₉ : Expr :=
  .lets𝕔 (.lit 1) { 0 ⇛
  .lets𝕔 (.alloc₁ x₀) { 1 ⇛
  .lam𝕔 { 2 ⇛
    .app₁ (
      .lam (
        .app₁ (
          .app₁ (
            .lam { 103 ⇛
            .lam { 104 ⇛
              .ifz₁ n (
                .load₂ (.code x₁)) (
                .lets (.store₂ (.code x₁) (.binary₂ .mul (.code x₂) (.load₂ (.code x₁)))) (
                .app₁ f (.binary₁ .sub n (.lit 1))))}}) (
            .fix₁ (
              .lam { 103 ⇛
              .lam { 104 ⇛
                .ifz₁ n (
                  .load₂ (.code x₁)) (
                  .lets (.store₂ (.code x₁) (.binary₂ .mul (.code x₂) (.load₂ (.code x₁)))) (
                  .app₁ f (.binary₁ .sub n (.lit 1))))}}))) (
          .bvar 0))) (
      .lit 2)}}}

def expr𝕩₀ : Expr :=
  .lets𝕔 (.lit 1) { 0 ⇛
  .lets𝕔 (.alloc₁ x₀) { 1 ⇛
  .lam𝕔 { 2 ⇛
    .app₁ (
      .app₁ (
        .lam { 103 ⇛
        .lam { 104 ⇛
          .ifz₁ n (
            .load₂ (.code x₁)) (
            .lets (.store₂ (.code x₁) (.binary₂ .mul (.code x₂) (.load₂ (.code x₁)))) (
            .app₁ f (.binary₁ .sub n (.lit 1))))}}) (
        .fix₁ (
          .lam { 103 ⇛
          .lam { 104 ⇛
            .ifz₁ n (
              .load₂ (.code x₁)) (
              .lets (.store₂ (.code x₁) (.binary₂ .mul (.code x₂) (.load₂ (.code x₁)))) (
              .app₁ f (.binary₁ .sub n (.lit 1))))}}))) (
      .lit 2)}}}

def expr𝕩₁ : Expr :=
  .lets𝕔 (.lit 1) { 0 ⇛
  .lets𝕔 (.alloc₁ x₀) { 1 ⇛
  .lam𝕔 { 2 ⇛
    .app₁ (
      .app₁ (
        .lam { 103 ⇛
        .lam { 104 ⇛
          .ifz₁ n (
            .load₂ (.code x₁)) (
            .lets (.store₂ (.code x₁) (.binary₂ .mul (.code x₂) (.load₂ (.code x₁)))) (
            .app₁ f (.binary₁ .sub n (.lit 1))))}}) (
        .lam (
          .app₁ (
            .app₁ (
              .lam { 103 ⇛
              .lam { 104 ⇛
                .ifz₁ n (
                  .load₂ (.code x₁)) (
                  .lets (.store₂ (.code x₁) (.binary₂ .mul (.code x₂) (.load₂ (.code x₁)))) (
                  .app₁ f (.binary₁ .sub n (.lit 1))))}}) (
              .fix₁ (
                .lam { 103 ⇛
                .lam { 104 ⇛
                  .ifz₁ n (
                    .load₂ (.code x₁)) (
                    .lets (.store₂ (.code x₁) (.binary₂ .mul (.code x₂) (.load₂ (.code x₁)))) (
                    .app₁ f (.binary₁ .sub n (.lit 1))))}}))) (
            .bvar 0)))) (
      .lit 2)}}}

def expr𝕩₂ : Expr :=
  .lets𝕔 (.lit 1) { 0 ⇛
  .lets𝕔 (.alloc₁ x₀) { 1 ⇛
  .lam𝕔 { 2 ⇛
    .app₁ (
      .lam { 104 ⇛
        .ifz₁ n (
          .load₂ (.code x₁)) (
          .lets (.store₂ (.code x₁) (.binary₂ .mul (.code x₂) (.load₂ (.code x₁)))) (
          .app₁ (
            .lam (
              .app₁ (
                .app₁ (
                  .lam { 103 ⇛
                  .lam { 104 ⇛
                    .ifz₁ n (
                      .load₂ (.code x₁)) (
                      .lets (.store₂ (.code x₁) (.binary₂ .mul (.code x₂) (.load₂ (.code x₁)))) (
                      .app₁ f (.binary₁ .sub n (.lit 1))))}}) (
                  .fix₁ (
                    .lam { 103 ⇛
                    .lam { 104 ⇛
                      .ifz₁ n (
                        .load₂ (.code x₁)) (
                        .lets (.store₂ (.code x₁) (.binary₂ .mul (.code x₂) (.load₂ (.code x₁)))) (
                        .app₁ f (.binary₁ .sub n (.lit 1))))}}))) (
                .bvar 0))) (
            .binary₁ .sub n (.lit 1))))}) (
      .lit 2)}}}

def expr𝕩₃ : Expr :=
  .lets𝕔 (.lit 1) { 0 ⇛
  .lets𝕔 (.alloc₁ x₀) { 1 ⇛
  .lam𝕔 { 2 ⇛
    .ifz₁ (.lit 2) (
      .load₂ (.code x₁)) (
      .lets (.store₂ (.code x₁) (.binary₂ .mul (.code x₂) (.load₂ (.code x₁)))) (
      .app₁ (
        .lam (
          .app₁ (
            .app₁ (
              .lam { 103 ⇛
              .lam { 104 ⇛
                .ifz₁ n (
                  .load₂ (.code x₁)) (
                  .lets (.store₂ (.code x₁) (.binary₂ .mul (.code x₂) (.load₂ (.code x₁)))) (
                  .app₁ f (.binary₁ .sub n (.lit 1))))}}) (
              .fix₁ (
                .lam { 103 ⇛
                .lam { 104 ⇛
                  .ifz₁ n (
                    .load₂ (.code x₁)) (
                    .lets (.store₂ (.code x₁) (.binary₂ .mul (.code x₂) (.load₂ (.code x₁)))) (
                    .app₁ f (.binary₁ .sub n (.lit 1))))}}))) (
            .bvar 0))) (
        .binary₁ .sub (.lit 2) (.lit 1))))}}}

def expr𝕩₄ : Expr :=
  .lets𝕔 (.lit 1) { 0 ⇛
  .lets𝕔 (.alloc₁ x₀) { 1 ⇛
  .lam𝕔 { 2 ⇛
    .lets (.store₂ (.code x₁) (.binary₂ .mul (.code x₂) (.load₂ (.code x₁)))) (
    .app₁ (
      .lam (
        .app₁ (
          .app₁ (
            .lam { 103 ⇛
            .lam { 104 ⇛
              .ifz₁ n (
                .load₂ (.code x₁)) (
                .lets (.store₂ (.code x₁) (.binary₂ .mul (.code x₂) (.load₂ (.code x₁)))) (
                .app₁ f (.binary₁ .sub n (.lit 1))))}}) (
            .fix₁ (
              .lam { 103 ⇛
              .lam { 104 ⇛
                .ifz₁ n (
                  .load₂ (.code x₁)) (
                  .lets (.store₂ (.code x₁) (.binary₂ .mul (.code x₂) (.load₂ (.code x₁)))) (
                  .app₁ f (.binary₁ .sub n (.lit 1))))}}))) (
          .bvar 0))) (
      .binary₁ .sub (.lit 2) (.lit 1)))}}}

def expr𝕩₅ : Expr :=
  .lets𝕔 (.lit 1) { 0 ⇛
  .lets𝕔 (.alloc₁ x₀) { 1 ⇛
  .lam𝕔 { 2 ⇛
    .lets (.store₂ (.code x₁) (.binary₂ .mul (.code x₂) (.reflect (.load₁ x₁)))) (
    .app₁ (
      .lam (
        .app₁ (
          .app₁ (
            .lam { 103 ⇛
            .lam { 104 ⇛
              .ifz₁ n (
                .load₂ (.code x₁)) (
                .lets (.store₂ (.code x₁) (.binary₂ .mul (.code x₂) (.load₂ (.code x₁)))) (
                .app₁ f (.binary₁ .sub n (.lit 1))))}}) (
            .fix₁ (
              .lam { 103 ⇛
              .lam { 104 ⇛
                .ifz₁ n (
                  .load₂ (.code x₁)) (
                  .lets (.store₂ (.code x₁) (.binary₂ .mul (.code x₂) (.load₂ (.code x₁)))) (
                  .app₁ f (.binary₁ .sub n (.lit 1))))}}))) (
          .bvar 0))) (
      .binary₁ .sub (.lit 2) (.lit 1)))}}}

def expr𝕩₆ : Expr :=
  .lets𝕔 (.lit 1) { 0 ⇛
  .lets𝕔 (.alloc₁ x₀) { 1 ⇛
  .lam𝕔 { 2 ⇛
    .lets𝕔 (.load₁ x₁) { 3 ⇛
    .lets (.store₂ (.code x₁) (.binary₂ .mul (.code x₂) (.code x₃))) (
    .app₁ (
      .lam (
        .app₁ (
          .app₁ (
            .lam { 103 ⇛
            .lam { 104 ⇛
              .ifz₁ n (
                .load₂ (.code x₁)) (
                .lets (.store₂ (.code x₁) (.binary₂ .mul (.code x₂) (.load₂ (.code x₁)))) (
                .app₁ f (.binary₁ .sub n (.lit 1))))}}) (
            .fix₁ (
              .lam { 103 ⇛
              .lam { 104 ⇛
                .ifz₁ n (
                  .load₂ (.code x₁)) (
                  .lets (.store₂ (.code x₁) (.binary₂ .mul (.code x₂) (.load₂ (.code x₁)))) (
                  .app₁ f (.binary₁ .sub n (.lit 1))))}}))) (
          .bvar 0))) (
      .binary₁ .sub (.lit 2) (.lit 1)))}}}}

def expr𝕩₇ : Expr :=
  .lets𝕔 (.lit 1) { 0 ⇛
  .lets𝕔 (.alloc₁ x₀) { 1 ⇛
  .lam𝕔 { 2 ⇛
    .lets𝕔 (.load₁ x₁) { 3 ⇛
    .lets (.store₂ (.code x₁) (.reflect (.binary₁ .mul x₂ x₃))) (
    .app₁ (
      .lam (
        .app₁ (
          .app₁ (
            .lam { 103 ⇛
            .lam { 104 ⇛
              .ifz₁ n (
                .load₂ (.code x₁)) (
                .lets (.store₂ (.code x₁) (.binary₂ .mul (.code x₂) (.load₂ (.code x₁)))) (
                .app₁ f (.binary₁ .sub n (.lit 1))))}}) (
            .fix₁ (
              .lam { 103 ⇛
              .lam { 104 ⇛
                .ifz₁ n (
                  .load₂ (.code x₁)) (
                  .lets (.store₂ (.code x₁) (.binary₂ .mul (.code x₂) (.load₂ (.code x₁)))) (
                  .app₁ f (.binary₁ .sub n (.lit 1))))}}))) (
          .bvar 0))) (
      .binary₁ .sub (.lit 2) (.lit 1)))}}}}

def expr𝕩₈ : Expr :=
  .lets𝕔 (.lit 1) { 0 ⇛
  .lets𝕔 (.alloc₁ x₀) { 1 ⇛
  .lam𝕔 { 2 ⇛
    .lets𝕔 (.load₁ x₁) { 3 ⇛
    .lets𝕔 (.binary₁ .mul x₂ x₃) { 4 ⇛
    .lets (.store₂ (.code x₁) (.code x₄)) (
    .app₁ (
      .lam (
        .app₁ (
          .app₁ (
            .lam { 103 ⇛
            .lam { 104 ⇛
              .ifz₁ n (
                .load₂ (.code x₁)) (
                .lets (.store₂ (.code x₁) (.binary₂ .mul (.code x₂) (.load₂ (.code x₁)))) (
                .app₁ f (.binary₁ .sub n (.lit 1))))}}) (
            .fix₁ (
              .lam { 103 ⇛
              .lam { 104 ⇛
                .ifz₁ n (
                  .load₂ (.code x₁)) (
                  .lets (.store₂ (.code x₁) (.binary₂ .mul (.code x₂) (.load₂ (.code x₁)))) (
                  .app₁ f (.binary₁ .sub n (.lit 1))))}}))) (
          .bvar 0))) (
      .binary₁ .sub (.lit 2) (.lit 1)))}}}}}

def expr𝕩₉ : Expr :=
  .lets𝕔 (.lit 1) { 0 ⇛
  .lets𝕔 (.alloc₁ x₀) { 1 ⇛
  .lam𝕔 { 2 ⇛
    .lets𝕔 (.load₁ x₁) { 3 ⇛
    .lets𝕔 (.binary₁ .mul x₂ x₃) { 4 ⇛
    .lets (.reflect (.store₁ x₁ x₄)) (
    .app₁ (
      .lam (
        .app₁ (
          .app₁ (
            .lam { 103 ⇛
            .lam { 104 ⇛
              .ifz₁ n (
                .load₂ (.code x₁)) (
                .lets (.store₂ (.code x₁) (.binary₂ .mul (.code x₂) (.load₂ (.code x₁)))) (
                .app₁ f (.binary₁ .sub n (.lit 1))))}}) (
            .fix₁ (
              .lam { 103 ⇛
              .lam { 104 ⇛
                .ifz₁ n (
                  .load₂ (.code x₁)) (
                  .lets (.store₂ (.code x₁) (.binary₂ .mul (.code x₂) (.load₂ (.code x₁)))) (
                  .app₁ f (.binary₁ .sub n (.lit 1))))}}))) (
          .bvar 0))) (
      .binary₁ .sub (.lit 2) (.lit 1)))}}}}}

def expr𝕩𝕩₀ : Expr :=
  .lets𝕔 (.lit 1) { 0 ⇛
  .lets𝕔 (.alloc₁ x₀) { 1 ⇛
  .lam𝕔 { 2 ⇛
    .lets𝕔 (.load₁ x₁) { 3 ⇛
    .lets𝕔 (.binary₁ .mul x₂ x₃) { 4 ⇛
    .lets𝕔 (.store₁ x₁ x₄) { 5 ⇛
    .lets (.code x₅) (
    .app₁ (
      .lam (
        .app₁ (
          .app₁ (
            .lam { 103 ⇛
            .lam { 104 ⇛
              .ifz₁ n (
                .load₂ (.code x₁)) (
                .lets (.store₂ (.code x₁) (.binary₂ .mul (.code x₂) (.load₂ (.code x₁)))) (
                .app₁ f (.binary₁ .sub n (.lit 1))))}}) (
            .fix₁ (
              .lam { 103 ⇛
              .lam { 104 ⇛
                .ifz₁ n (
                  .load₂ (.code x₁)) (
                  .lets (.store₂ (.code x₁) (.binary₂ .mul (.code x₂) (.load₂ (.code x₁)))) (
                  .app₁ f (.binary₁ .sub n (.lit 1))))}}))) (
          .bvar 0))) (
      .binary₁ .sub (.lit 2) (.lit 1)))}}}}}}

def expr𝕩𝕩₁ : Expr :=
  .lets𝕔 (.lit 1) { 0 ⇛
  .lets𝕔 (.alloc₁ x₀) { 1 ⇛
  .lam𝕔 { 2 ⇛
    .lets𝕔 (.load₁ x₁) { 3 ⇛
    .lets𝕔 (.binary₁ .mul x₂ x₃) { 4 ⇛
    .lets𝕔 (.store₁ x₁ x₄) { 5 ⇛
    .app₁ (
      .lam (
        .app₁ (
          .app₁ (
            .lam { 103 ⇛
            .lam { 104 ⇛
              .ifz₁ n (
                .load₂ (.code x₁)) (
                .lets (.store₂ (.code x₁) (.binary₂ .mul (.code x₂) (.load₂ (.code x₁)))) (
                .app₁ f (.binary₁ .sub n (.lit 1))))}}) (
            .fix₁ (
              .lam { 103 ⇛
              .lam { 104 ⇛
                .ifz₁ n (
                  .load₂ (.code x₁)) (
                  .lets (.store₂ (.code x₁) (.binary₂ .mul (.code x₂) (.load₂ (.code x₁)))) (
                  .app₁ f (.binary₁ .sub n (.lit 1))))}}))) (
          .bvar 0))) (
      .binary₁ .sub (.lit 2) (.lit 1))}}}}}}

def expr𝕩𝕩₂ : Expr :=
  .lets𝕔 (.lit 1) { 0 ⇛
  .lets𝕔 (.alloc₁ x₀) { 1 ⇛
  .lam𝕔 { 2 ⇛
    .lets𝕔 (.load₁ x₁) { 3 ⇛
    .lets𝕔 (.binary₁ .mul x₂ x₃) { 4 ⇛
    .lets𝕔 (.store₁ x₁ x₄) { 5 ⇛
    .app₁ (
      .lam (
        .app₁ (
          .app₁ (
            .lam { 103 ⇛
            .lam { 104 ⇛
              .ifz₁ n (
                .load₂ (.code x₁)) (
                .lets (.store₂ (.code x₁) (.binary₂ .mul (.code x₂) (.load₂ (.code x₁)))) (
                .app₁ f (.binary₁ .sub n (.lit 1))))}}) (
            .fix₁ (
              .lam { 103 ⇛
              .lam { 104 ⇛
                .ifz₁ n (
                  .load₂ (.code x₁)) (
                  .lets (.store₂ (.code x₁) (.binary₂ .mul (.code x₂) (.load₂ (.code x₁)))) (
                  .app₁ f (.binary₁ .sub n (.lit 1))))}}))) (
          .bvar 0))) (
      .lit 1)}}}}}}

def expr𝕩𝕩₃ : Expr :=
  .lets𝕔 (.lit 1) { 0 ⇛
  .lets𝕔 (.alloc₁ x₀) { 1 ⇛
  .lam𝕔 { 2 ⇛
    .lets𝕔 (.load₁ x₁) { 3 ⇛
    .lets𝕔 (.binary₁ .mul x₂ x₃) { 4 ⇛
    .lets𝕔 (.store₁ x₁ x₄) { 5 ⇛
      .app₁ (
        .app₁ (
          .lam { 103 ⇛
          .lam { 104 ⇛
            .ifz₁ n (
              .load₂ (.code x₁)) (
              .lets (.store₂ (.code x₁) (.binary₂ .mul (.code x₂) (.load₂ (.code x₁)))) (
              .app₁ f (.binary₁ .sub n (.lit 1))))}}) (
          .fix₁ (
            .lam { 103 ⇛
            .lam { 104 ⇛
              .ifz₁ n (
                .load₂ (.code x₁)) (
                .lets (.store₂ (.code x₁) (.binary₂ .mul (.code x₂) (.load₂ (.code x₁)))) (
                .app₁ f (.binary₁ .sub n (.lit 1))))}}))) (
        .lit 1)}}}}}}

def expr𝕩𝕩₄ : Expr :=
  .lets𝕔 (.lit 1) { 0 ⇛
  .lets𝕔 (.alloc₁ x₀) { 1 ⇛
  .lam𝕔 { 2 ⇛
    .lets𝕔 (.load₁ x₁) { 3 ⇛
    .lets𝕔 (.binary₁ .mul x₂ x₃) { 4 ⇛
    .lets𝕔 (.store₁ x₁ x₄) { 5 ⇛
      .app₁ (
        .app₁ (
          .lam { 103 ⇛
          .lam { 104 ⇛
            .ifz₁ n (
              .load₂ (.code x₁)) (
              .lets (.store₂ (.code x₁) (.binary₂ .mul (.code x₂) (.load₂ (.code x₁)))) (
              .app₁ f (.binary₁ .sub n (.lit 1))))}}) (
          .lam (
            .app₁ (
              .app₁ (
                .lam { 103 ⇛
                .lam { 104 ⇛
                  .ifz₁ n (
                    .load₂ (.code x₁)) (
                    .lets (.store₂ (.code x₁) (.binary₂ .mul (.code x₂) (.load₂ (.code x₁)))) (
                    .app₁ f (.binary₁ .sub n (.lit 1))))}}) (
                .fix₁ (
                  .lam { 103 ⇛
                  .lam { 104 ⇛
                    .ifz₁ n (
                      .load₂ (.code x₁)) (
                      .lets (.store₂ (.code x₁) (.binary₂ .mul (.code x₂) (.load₂ (.code x₁)))) (
                      .app₁ f (.binary₁ .sub n (.lit 1))))}}))) (
              .bvar 0)))) (
        .lit 1)}}}}}}

def expr𝕩𝕩₅ : Expr :=
  .lets𝕔 (.lit 1) { 0 ⇛
  .lets𝕔 (.alloc₁ x₀) { 1 ⇛
  .lam𝕔 { 2 ⇛
    .lets𝕔 (.load₁ x₁) { 3 ⇛
    .lets𝕔 (.binary₁ .mul x₂ x₃) { 4 ⇛
    .lets𝕔 (.store₁ x₁ x₄) { 5 ⇛
      .app₁ (
        .lam { 104 ⇛
          .ifz₁ n (
            .load₂ (.code x₁)) (
            .lets (.store₂ (.code x₁) (.binary₂ .mul (.code x₂) (.load₂ (.code x₁)))) (
            .app₁ (
              .lam (
                .app₁ (
                  .app₁ (
                    .lam { 103 ⇛
                    .lam { 104 ⇛
                      .ifz₁ n (
                        .load₂ (.code x₁)) (
                        .lets (.store₂ (.code x₁) (.binary₂ .mul (.code x₂) (.load₂ (.code x₁)))) (
                        .app₁ f (.binary₁ .sub n (.lit 1))))}}) (
                    .fix₁ (
                      .lam { 103 ⇛
                      .lam { 104 ⇛
                        .ifz₁ n (
                          .load₂ (.code x₁)) (
                          .lets (.store₂ (.code x₁) (.binary₂ .mul (.code x₂) (.load₂ (.code x₁)))) (
                          .app₁ f (.binary₁ .sub n (.lit 1))))}}))) (
                  .bvar 0))) (
              .binary₁ .sub n (.lit 1))))}) (
        .lit 1)}}}}}}

def expr𝕩𝕩₆ : Expr :=
  .lets𝕔 (.lit 1) { 0 ⇛
  .lets𝕔 (.alloc₁ x₀) { 1 ⇛
  .lam𝕔 { 2 ⇛
    .lets𝕔 (.load₁ x₁) { 3 ⇛
    .lets𝕔 (.binary₁ .mul x₂ x₃) { 4 ⇛
    .lets𝕔 (.store₁ x₁ x₄) { 5 ⇛
      .ifz₁ (.lit 1) (
        .load₂ (.code x₁)) (
        .lets (.store₂ (.code x₁) (.binary₂ .mul (.code x₂) (.load₂ (.code x₁)))) (
        .app₁ (
          .lam (
            .app₁ (
              .app₁ (
                .lam { 103 ⇛
                .lam { 104 ⇛
                  .ifz₁ n (
                    .load₂ (.code x₁)) (
                    .lets (.store₂ (.code x₁) (.binary₂ .mul (.code x₂) (.load₂ (.code x₁)))) (
                    .app₁ f (.binary₁ .sub n (.lit 1))))}}) (
                .fix₁ (
                  .lam { 103 ⇛
                  .lam { 104 ⇛
                    .ifz₁ n (
                      .load₂ (.code x₁)) (
                      .lets (.store₂ (.code x₁) (.binary₂ .mul (.code x₂) (.load₂ (.code x₁)))) (
                      .app₁ f (.binary₁ .sub n (.lit 1))))}}))) (
              .bvar 0))) (
          .binary₁ .sub (.lit 1) (.lit 1))))}}}}}}

def expr𝕩𝕩₇ : Expr :=
  .lets𝕔 (.lit 1) { 0 ⇛
  .lets𝕔 (.alloc₁ x₀) { 1 ⇛
  .lam𝕔 { 2 ⇛
    .lets𝕔 (.load₁ x₁) { 3 ⇛
    .lets𝕔 (.binary₁ .mul x₂ x₃) { 4 ⇛
    .lets𝕔 (.store₁ x₁ x₄) { 5 ⇛
      .lets (.store₂ (.code x₁) (.binary₂ .mul (.code x₂) (.load₂ (.code x₁)))) (
      .app₁ (
        .lam (
          .app₁ (
            .app₁ (
              .lam { 103 ⇛
              .lam { 104 ⇛
                .ifz₁ n (
                  .load₂ (.code x₁)) (
                  .lets (.store₂ (.code x₁) (.binary₂ .mul (.code x₂) (.load₂ (.code x₁)))) (
                  .app₁ f (.binary₁ .sub n (.lit 1))))}}) (
              .fix₁ (
                .lam { 103 ⇛
                .lam { 104 ⇛
                  .ifz₁ n (
                    .load₂ (.code x₁)) (
                    .lets (.store₂ (.code x₁) (.binary₂ .mul (.code x₂) (.load₂ (.code x₁)))) (
                    .app₁ f (.binary₁ .sub n (.lit 1))))}}))) (
            .bvar 0))) (
        .binary₁ .sub (.lit 1) (.lit 1)))}}}}}}

def expr𝕩𝕩₈ : Expr :=
  .lets𝕔 (.lit 1) { 0 ⇛
  .lets𝕔 (.alloc₁ x₀) { 1 ⇛
  .lam𝕔 { 2 ⇛
    .lets𝕔 (.load₁ x₁) { 3 ⇛
    .lets𝕔 (.binary₁ .mul x₂ x₃) { 4 ⇛
    .lets𝕔 (.store₁ x₁ x₄) { 5 ⇛
      .lets (.store₂ (.code x₁) (.binary₂ .mul (.code x₂) (.reflect (.load₁ x₁)))) (
      .app₁ (
        .lam (
          .app₁ (
            .app₁ (
              .lam { 103 ⇛
              .lam { 104 ⇛
                .ifz₁ n (
                  .load₂ (.code x₁)) (
                  .lets (.store₂ (.code x₁) (.binary₂ .mul (.code x₂) (.load₂ (.code x₁)))) (
                  .app₁ f (.binary₁ .sub n (.lit 1))))}}) (
              .fix₁ (
                .lam { 103 ⇛
                .lam { 104 ⇛
                  .ifz₁ n (
                    .load₂ (.code x₁)) (
                    .lets (.store₂ (.code x₁) (.binary₂ .mul (.code x₂) (.load₂ (.code x₁)))) (
                    .app₁ f (.binary₁ .sub n (.lit 1))))}}))) (
            .bvar 0))) (
        .binary₁ .sub (.lit 1) (.lit 1)))}}}}}}

def expr𝕩𝕩₉ : Expr :=
  .lets𝕔 (.lit 1) { 0 ⇛
  .lets𝕔 (.alloc₁ x₀) { 1 ⇛
  .lam𝕔 { 2 ⇛
    .lets𝕔 (.load₁ x₁) { 3 ⇛
    .lets𝕔 (.binary₁ .mul x₂ x₃) { 4 ⇛
    .lets𝕔 (.store₁ x₁ x₄) { 5 ⇛
    .lets𝕔 (.load₁ x₁) { 6 ⇛
      .lets (.store₂ (.code x₁) (.binary₂ .mul (.code x₂) (.code x₆))) (
      .app₁ (
        .lam (
          .app₁ (
            .app₁ (
              .lam { 103 ⇛
              .lam { 104 ⇛
                .ifz₁ n (
                  .load₂ (.code x₁)) (
                  .lets (.store₂ (.code x₁) (.binary₂ .mul (.code x₂) (.load₂ (.code x₁)))) (
                  .app₁ f (.binary₁ .sub n (.lit 1))))}}) (
              .fix₁ (
                .lam { 103 ⇛
                .lam { 104 ⇛
                  .ifz₁ n (
                    .load₂ (.code x₁)) (
                    .lets (.store₂ (.code x₁) (.binary₂ .mul (.code x₂) (.load₂ (.code x₁)))) (
                    .app₁ f (.binary₁ .sub n (.lit 1))))}}))) (
            .bvar 0))) (
        .binary₁ .sub (.lit 1) (.lit 1)))}}}}}}}

def expr𝕩𝕩𝕩₀ : Expr :=
  .lets𝕔 (.lit 1) { 0 ⇛
  .lets𝕔 (.alloc₁ x₀) { 1 ⇛
  .lam𝕔 { 2 ⇛
    .lets𝕔 (.load₁ x₁) { 3 ⇛
    .lets𝕔 (.binary₁ .mul x₂ x₃) { 4 ⇛
    .lets𝕔 (.store₁ x₁ x₄) { 5 ⇛
    .lets𝕔 (.load₁ x₁) { 6 ⇛
      .lets (.store₂ (.code x₁) (.reflect (.binary₁ .mul x₂ x₆))) (
      .app₁ (
        .lam (
          .app₁ (
            .app₁ (
              .lam { 103 ⇛
              .lam { 104 ⇛
                .ifz₁ n (
                  .load₂ (.code x₁)) (
                  .lets (.store₂ (.code x₁) (.binary₂ .mul (.code x₂) (.load₂ (.code x₁)))) (
                  .app₁ f (.binary₁ .sub n (.lit 1))))}}) (
              .fix₁ (
                .lam { 103 ⇛
                .lam { 104 ⇛
                  .ifz₁ n (
                    .load₂ (.code x₁)) (
                    .lets (.store₂ (.code x₁) (.binary₂ .mul (.code x₂) (.load₂ (.code x₁)))) (
                    .app₁ f (.binary₁ .sub n (.lit 1))))}}))) (
            .bvar 0))) (
        .binary₁ .sub (.lit 1) (.lit 1)))}}}}}}}

def expr𝕩𝕩𝕩₁ : Expr :=
  .lets𝕔 (.lit 1) { 0 ⇛
  .lets𝕔 (.alloc₁ x₀) { 1 ⇛
  .lam𝕔 { 2 ⇛
    .lets𝕔 (.load₁ x₁) { 3 ⇛
    .lets𝕔 (.binary₁ .mul x₂ x₃) { 4 ⇛
    .lets𝕔 (.store₁ x₁ x₄) { 5 ⇛
    .lets𝕔 (.load₁ x₁) { 6 ⇛
    .lets𝕔 (.binary₁ .mul x₂ x₆) { 7 ⇛
      .lets (.store₂ (.code x₁) (.code x₇)) (
      .app₁ (
        .lam (
          .app₁ (
            .app₁ (
              .lam { 103 ⇛
              .lam { 104 ⇛
                .ifz₁ n (
                  .load₂ (.code x₁)) (
                  .lets (.store₂ (.code x₁) (.binary₂ .mul (.code x₂) (.load₂ (.code x₁)))) (
                  .app₁ f (.binary₁ .sub n (.lit 1))))}}) (
              .fix₁ (
                .lam { 103 ⇛
                .lam { 104 ⇛
                  .ifz₁ n (
                    .load₂ (.code x₁)) (
                    .lets (.store₂ (.code x₁) (.binary₂ .mul (.code x₂) (.load₂ (.code x₁)))) (
                    .app₁ f (.binary₁ .sub n (.lit 1))))}}))) (
            .bvar 0))) (
        .binary₁ .sub (.lit 1) (.lit 1)))}}}}}}}}

def expr𝕩𝕩𝕩₂ : Expr :=
  .lets𝕔 (.lit 1) { 0 ⇛
  .lets𝕔 (.alloc₁ x₀) { 1 ⇛
  .lam𝕔 { 2 ⇛
    .lets𝕔 (.load₁ x₁) { 3 ⇛
    .lets𝕔 (.binary₁ .mul x₂ x₃) { 4 ⇛
    .lets𝕔 (.store₁ x₁ x₄) { 5 ⇛
    .lets𝕔 (.load₁ x₁) { 6 ⇛
    .lets𝕔 (.binary₁ .mul x₂ x₆) { 7 ⇛
      .lets (.reflect (.store₁ x₁ x₇)) (
      .app₁ (
        .lam (
          .app₁ (
            .app₁ (
              .lam { 103 ⇛
              .lam { 104 ⇛
                .ifz₁ n (
                  .load₂ (.code x₁)) (
                  .lets (.store₂ (.code x₁) (.binary₂ .mul (.code x₂) (.load₂ (.code x₁)))) (
                  .app₁ f (.binary₁ .sub n (.lit 1))))}}) (
              .fix₁ (
                .lam { 103 ⇛
                .lam { 104 ⇛
                  .ifz₁ n (
                    .load₂ (.code x₁)) (
                    .lets (.store₂ (.code x₁) (.binary₂ .mul (.code x₂) (.load₂ (.code x₁)))) (
                    .app₁ f (.binary₁ .sub n (.lit 1))))}}))) (
            .bvar 0))) (
        .binary₁ .sub (.lit 1) (.lit 1)))}}}}}}}}

def expr𝕩𝕩𝕩₃ : Expr :=
  .lets𝕔 (.lit 1) { 0 ⇛
  .lets𝕔 (.alloc₁ x₀) { 1 ⇛
  .lam𝕔 { 2 ⇛
    .lets𝕔 (.load₁ x₁) { 3 ⇛
    .lets𝕔 (.binary₁ .mul x₂ x₃) { 4 ⇛
    .lets𝕔 (.store₁ x₁ x₄) { 5 ⇛
    .lets𝕔 (.load₁ x₁) { 6 ⇛
    .lets𝕔 (.binary₁ .mul x₂ x₆) { 7 ⇛
    .lets𝕔 (.store₁ x₁ x₇) { 8 ⇛
      .lets (.code x₈) (
      .app₁ (
        .lam (
          .app₁ (
            .app₁ (
              .lam { 103 ⇛
              .lam { 104 ⇛
                .ifz₁ n (
                  .load₂ (.code x₁)) (
                  .lets (.store₂ (.code x₁) (.binary₂ .mul (.code x₂) (.load₂ (.code x₁)))) (
                  .app₁ f (.binary₁ .sub n (.lit 1))))}}) (
              .fix₁ (
                .lam { 103 ⇛
                .lam { 104 ⇛
                  .ifz₁ n (
                    .load₂ (.code x₁)) (
                    .lets (.store₂ (.code x₁) (.binary₂ .mul (.code x₂) (.load₂ (.code x₁)))) (
                    .app₁ f (.binary₁ .sub n (.lit 1))))}}))) (
            .bvar 0))) (
        .binary₁ .sub (.lit 1) (.lit 1)))}}}}}}}}}

def expr𝕩𝕩𝕩₄ : Expr :=
  .lets𝕔 (.lit 1) { 0 ⇛
  .lets𝕔 (.alloc₁ x₀) { 1 ⇛
  .lam𝕔 { 2 ⇛
    .lets𝕔 (.load₁ x₁) { 3 ⇛
    .lets𝕔 (.binary₁ .mul x₂ x₃) { 4 ⇛
    .lets𝕔 (.store₁ x₁ x₄) { 5 ⇛
    .lets𝕔 (.load₁ x₁) { 6 ⇛
    .lets𝕔 (.binary₁ .mul x₂ x₆) { 7 ⇛
    .lets𝕔 (.store₁ x₁ x₇) { 8 ⇛
      .app₁ (
        .lam (
          .app₁ (
            .app₁ (
              .lam { 103 ⇛
              .lam { 104 ⇛
                .ifz₁ n (
                  .load₂ (.code x₁)) (
                  .lets (.store₂ (.code x₁) (.binary₂ .mul (.code x₂) (.load₂ (.code x₁)))) (
                  .app₁ f (.binary₁ .sub n (.lit 1))))}}) (
              .fix₁ (
                .lam { 103 ⇛
                .lam { 104 ⇛
                  .ifz₁ n (
                    .load₂ (.code x₁)) (
                    .lets (.store₂ (.code x₁) (.binary₂ .mul (.code x₂) (.load₂ (.code x₁)))) (
                    .app₁ f (.binary₁ .sub n (.lit 1))))}}))) (
            .bvar 0))) (
        .binary₁ .sub (.lit 1) (.lit 1))}}}}}}}}}

def expr𝕩𝕩𝕩₅ : Expr :=
  .lets𝕔 (.lit 1) { 0 ⇛
  .lets𝕔 (.alloc₁ x₀) { 1 ⇛
  .lam𝕔 { 2 ⇛
    .lets𝕔 (.load₁ x₁) { 3 ⇛
    .lets𝕔 (.binary₁ .mul x₂ x₃) { 4 ⇛
    .lets𝕔 (.store₁ x₁ x₄) { 5 ⇛
    .lets𝕔 (.load₁ x₁) { 6 ⇛
    .lets𝕔 (.binary₁ .mul x₂ x₆) { 7 ⇛
    .lets𝕔 (.store₁ x₁ x₇) { 8 ⇛
      .app₁ (
        .lam (
          .app₁ (
            .app₁ (
              .lam { 103 ⇛
              .lam { 104 ⇛
                .ifz₁ n (
                  .load₂ (.code x₁)) (
                  .lets (.store₂ (.code x₁) (.binary₂ .mul (.code x₂) (.load₂ (.code x₁)))) (
                  .app₁ f (.binary₁ .sub n (.lit 1))))}}) (
              .fix₁ (
                .lam { 103 ⇛
                .lam { 104 ⇛
                  .ifz₁ n (
                    .load₂ (.code x₁)) (
                    .lets (.store₂ (.code x₁) (.binary₂ .mul (.code x₂) (.load₂ (.code x₁)))) (
                    .app₁ f (.binary₁ .sub n (.lit 1))))}}))) (
            .bvar 0))) (
        .lit 0)}}}}}}}}}

def expr𝕩𝕩𝕩₆ : Expr :=
  .lets𝕔 (.lit 1) { 0 ⇛
  .lets𝕔 (.alloc₁ x₀) { 1 ⇛
  .lam𝕔 { 2 ⇛
    .lets𝕔 (.load₁ x₁) { 3 ⇛
    .lets𝕔 (.binary₁ .mul x₂ x₃) { 4 ⇛
    .lets𝕔 (.store₁ x₁ x₄) { 5 ⇛
    .lets𝕔 (.load₁ x₁) { 6 ⇛
    .lets𝕔 (.binary₁ .mul x₂ x₆) { 7 ⇛
    .lets𝕔 (.store₁ x₁ x₇) { 8 ⇛
      .app₁ (
        .app₁ (
          .lam { 103 ⇛
          .lam { 104 ⇛
            .ifz₁ n (
              .load₂ (.code x₁)) (
              .lets (.store₂ (.code x₁) (.binary₂ .mul (.code x₂) (.load₂ (.code x₁)))) (
              .app₁ f (.binary₁ .sub n (.lit 1))))}}) (
          .fix₁ (
            .lam { 103 ⇛
            .lam { 104 ⇛
              .ifz₁ n (
                .load₂ (.code x₁)) (
                .lets (.store₂ (.code x₁) (.binary₂ .mul (.code x₂) (.load₂ (.code x₁)))) (
                .app₁ f (.binary₁ .sub n (.lit 1))))}}))) (
        .lit 0)}}}}}}}}}

def expr𝕩𝕩𝕩₇ : Expr :=
  .lets𝕔 (.lit 1) { 0 ⇛
  .lets𝕔 (.alloc₁ x₀) { 1 ⇛
  .lam𝕔 { 2 ⇛
    .lets𝕔 (.load₁ x₁) { 3 ⇛
    .lets𝕔 (.binary₁ .mul x₂ x₃) { 4 ⇛
    .lets𝕔 (.store₁ x₁ x₄) { 5 ⇛
    .lets𝕔 (.load₁ x₁) { 6 ⇛
    .lets𝕔 (.binary₁ .mul x₂ x₆) { 7 ⇛
    .lets𝕔 (.store₁ x₁ x₇) { 8 ⇛
      .app₁ (
        .app₁ (
          .lam { 103 ⇛
          .lam { 104 ⇛
            .ifz₁ n (
              .load₂ (.code x₁)) (
              .lets (.store₂ (.code x₁) (.binary₂ .mul (.code x₂) (.load₂ (.code x₁)))) (
              .app₁ f (.binary₁ .sub n (.lit 1))))}}) (
          .lam (
            .app₁ (
              .app₁ (
                .lam { 103 ⇛
                .lam { 104 ⇛
                  .ifz₁ n (
                    .load₂ (.code x₁)) (
                    .lets (.store₂ (.code x₁) (.binary₂ .mul (.code x₂) (.load₂ (.code x₁)))) (
                    .app₁ f (.binary₁ .sub n (.lit 1))))}}) (
                .fix₁ (
                  .lam { 103 ⇛
                  .lam { 104 ⇛
                    .ifz₁ n (
                      .load₂ (.code x₁)) (
                      .lets (.store₂ (.code x₁) (.binary₂ .mul (.code x₂) (.load₂ (.code x₁)))) (
                      .app₁ f (.binary₁ .sub n (.lit 1))))}}))) (
              .bvar 0)))) (
        .lit 0)}}}}}}}}}

def expr𝕩𝕩𝕩₈ : Expr :=
  .lets𝕔 (.lit 1) { 0 ⇛
  .lets𝕔 (.alloc₁ x₀) { 1 ⇛
  .lam𝕔 { 2 ⇛
    .lets𝕔 (.load₁ x₁) { 3 ⇛
    .lets𝕔 (.binary₁ .mul x₂ x₃) { 4 ⇛
    .lets𝕔 (.store₁ x₁ x₄) { 5 ⇛
    .lets𝕔 (.load₁ x₁) { 6 ⇛
    .lets𝕔 (.binary₁ .mul x₂ x₆) { 7 ⇛
    .lets𝕔 (.store₁ x₁ x₇) { 8 ⇛
      .app₁ (
        .lam { 104 ⇛
          .ifz₁ n (
            .load₂ (.code x₁)) (
            .lets (.store₂ (.code x₁) (.binary₂ .mul (.code x₂) (.load₂ (.code x₁)))) (
            .app₁ (
              .lam (
                .app₁ (
                  .app₁ (
                    .lam { 103 ⇛
                    .lam { 104 ⇛
                      .ifz₁ n (
                        .load₂ (.code x₁)) (
                        .lets (.store₂ (.code x₁) (.binary₂ .mul (.code x₂) (.load₂ (.code x₁)))) (
                        .app₁ f (.binary₁ .sub n (.lit 1))))}}) (
                    .fix₁ (
                      .lam { 103 ⇛
                      .lam { 104 ⇛
                        .ifz₁ n (
                          .load₂ (.code x₁)) (
                          .lets (.store₂ (.code x₁) (.binary₂ .mul (.code x₂) (.load₂ (.code x₁)))) (
                          .app₁ f (.binary₁ .sub n (.lit 1))))}}))) (
                  .bvar 0))) (
              .binary₁ .sub n (.lit 1))))}) (
        .lit 0)}}}}}}}}}

def expr𝕩𝕩𝕩₉ : Expr :=
  .lets𝕔 (.lit 1) { 0 ⇛
  .lets𝕔 (.alloc₁ x₀) { 1 ⇛
  .lam𝕔 { 2 ⇛
    .lets𝕔 (.load₁ x₁) { 3 ⇛
    .lets𝕔 (.binary₁ .mul x₂ x₃) { 4 ⇛
    .lets𝕔 (.store₁ x₁ x₄) { 5 ⇛
    .lets𝕔 (.load₁ x₁) { 6 ⇛
    .lets𝕔 (.binary₁ .mul x₂ x₆) { 7 ⇛
    .lets𝕔 (.store₁ x₁ x₇) { 8 ⇛
      .ifz₁ (.lit 0) (
        .load₂ (.code x₁)) (
        .lets (.store₂ (.code x₁) (.binary₂ .mul (.code x₂) (.load₂ (.code x₁)))) (
        .app₁ (
          .lam (
            .app₁ (
              .app₁ (
                .lam { 103 ⇛
                .lam { 104 ⇛
                  .ifz₁ n (
                    .load₂ (.code x₁)) (
                    .lets (.store₂ (.code x₁) (.binary₂ .mul (.code x₂) (.load₂ (.code x₁)))) (
                    .app₁ f (.binary₁ .sub n (.lit 1))))}}) (
                .fix₁ (
                  .lam { 103 ⇛
                  .lam { 104 ⇛
                    .ifz₁ n (
                      .load₂ (.code x₁)) (
                      .lets (.store₂ (.code x₁) (.binary₂ .mul (.code x₂) (.load₂ (.code x₁)))) (
                      .app₁ f (.binary₁ .sub n (.lit 1))))}}))) (
              .bvar 0))) (
          .binary₁ .sub (.lit 0) (.lit 1))))}}}}}}}}}

def expr𝕩𝕩𝕩𝕩₀ : Expr :=
  .lets𝕔 (.lit 1) { 0 ⇛
  .lets𝕔 (.alloc₁ x₀) { 1 ⇛
  .lam𝕔 { 2 ⇛
    .lets𝕔 (.load₁ x₁) { 3 ⇛
    .lets𝕔 (.binary₁ .mul x₂ x₃) { 4 ⇛
    .lets𝕔 (.store₁ x₁ x₄) { 5 ⇛
    .lets𝕔 (.load₁ x₁) { 6 ⇛
    .lets𝕔 (.binary₁ .mul x₂ x₆) { 7 ⇛
    .lets𝕔 (.store₁ x₁ x₇) { 8 ⇛
      .load₂ (.code x₁)}}}}}}}}}

def expr𝕩𝕩𝕩𝕩₁ : Expr :=
  .lets𝕔 (.lit 1) { 0 ⇛
  .lets𝕔 (.alloc₁ x₀) { 1 ⇛
  .lam𝕔 { 2 ⇛
    .lets𝕔 (.load₁ x₁) { 3 ⇛
    .lets𝕔 (.binary₁ .mul x₂ x₃) { 4 ⇛
    .lets𝕔 (.store₁ x₁ x₄) { 5 ⇛
    .lets𝕔 (.load₁ x₁) { 6 ⇛
    .lets𝕔 (.binary₁ .mul x₂ x₆) { 7 ⇛
    .lets𝕔 (.store₁ x₁ x₇) { 8 ⇛
      .reflect (.load₁ x₁)}}}}}}}}}

def expr𝕩𝕩𝕩𝕩₂ : Expr :=
  .lets𝕔 (.lit 1) { 0 ⇛
  .lets𝕔 (.alloc₁ x₀) { 1 ⇛
  .lam𝕔 { 2 ⇛
    .lets𝕔 (.load₁ x₁) { 3 ⇛
    .lets𝕔 (.binary₁ .mul x₂ x₃) { 4 ⇛
    .lets𝕔 (.store₁ x₁ x₄) { 5 ⇛
    .lets𝕔 (.load₁ x₁) { 6 ⇛
    .lets𝕔 (.binary₁ .mul x₂ x₆) { 7 ⇛
    .lets𝕔 (.store₁ x₁ x₇) { 8 ⇛
    .lets𝕔 (.load₁ x₁) { 9 ⇛
      .code x₉}}}}}}}}}}

def expr𝕩𝕩𝕩𝕩₃ : Expr :=
  .lets𝕔 (.lit 1) { 0 ⇛
  .lets𝕔 (.alloc₁ x₀) { 1 ⇛
  .lam𝕔 { 2 ⇛
    .lets𝕔 (.load₁ x₁) { 3 ⇛
    .lets𝕔 (.binary₁ .mul x₂ x₃) { 4 ⇛
    .lets𝕔 (.store₁ x₁ x₄) { 5 ⇛
    .lets𝕔 (.load₁ x₁) { 6 ⇛
    .lets𝕔 (.binary₁ .mul x₂ x₆) { 7 ⇛
    .lets𝕔 (.store₁ x₁ x₇) { 8 ⇛
      .code (
        .lets (.load₁ x₁) { 9 ⇛
        x₉}
      )}}}}}}}}}

def expr𝕩𝕩𝕩𝕩₄ : Expr :=
  .lets𝕔 (.lit 1) { 0 ⇛
  .lets𝕔 (.alloc₁ x₀) { 1 ⇛
  .lam𝕔 { 2 ⇛
    .lets𝕔 (.load₁ x₁) { 3 ⇛
    .lets𝕔 (.binary₁ .mul x₂ x₃) { 4 ⇛
    .lets𝕔 (.store₁ x₁ x₄) { 5 ⇛
    .lets𝕔 (.load₁ x₁) { 6 ⇛
    .lets𝕔 (.binary₁ .mul x₂ x₆) { 7 ⇛
      .code (
        .lets (.store₁ x₁ x₇) { 8 ⇛
        .lets (.load₁ x₁) { 9 ⇛
        x₉}}
      )}}}}}}}}

def expr𝕩𝕩𝕩𝕩₅ : Expr :=
  .lets𝕔 (.lit 1) { 0 ⇛
  .lets𝕔 (.alloc₁ x₀) { 1 ⇛
  .lam𝕔 { 2 ⇛
    .lets𝕔 (.load₁ x₁) { 3 ⇛
    .lets𝕔 (.binary₁ .mul x₂ x₃) { 4 ⇛
    .lets𝕔 (.store₁ x₁ x₄) { 5 ⇛
    .lets𝕔 (.load₁ x₁) { 6 ⇛
      .code (
        .lets (.binary₁ .mul x₂ x₆) { 7 ⇛
        .lets (.store₁ x₁ x₇) { 8 ⇛
        .lets (.load₁ x₁) { 9 ⇛
        x₉}}}
      )}}}}}}}

def expr𝕩𝕩𝕩𝕩₆ : Expr :=
  .lets𝕔 (.lit 1) { 0 ⇛
  .lets𝕔 (.alloc₁ x₀) { 1 ⇛
  .lam𝕔 { 2 ⇛
    .lets𝕔 (.load₁ x₁) { 3 ⇛
    .lets𝕔 (.binary₁ .mul x₂ x₃) { 4 ⇛
    .lets𝕔 (.store₁ x₁ x₄) { 5 ⇛
      .code (
        .lets (.load₁ x₁) { 6 ⇛
        .lets (.binary₁ .mul x₂ x₆) { 7 ⇛
        .lets (.store₁ x₁ x₇) { 8 ⇛
        .lets (.load₁ x₁) { 9 ⇛
        x₉}}}}
      )}}}}}}

def expr𝕩𝕩𝕩𝕩₇ : Expr :=
  .lets𝕔 (.lit 1) { 0 ⇛
  .lets𝕔 (.alloc₁ x₀) { 1 ⇛
  .lam𝕔 { 2 ⇛
    .lets𝕔 (.load₁ x₁) { 3 ⇛
    .lets𝕔 (.binary₁ .mul x₂ x₃) { 4 ⇛
      .code (
        .lets (.store₁ x₁ x₄) { 5 ⇛
        .lets (.load₁ x₁) { 6 ⇛
        .lets (.binary₁ .mul x₂ x₆) { 7 ⇛
        .lets (.store₁ x₁ x₇) { 8 ⇛
        .lets (.load₁ x₁) { 9 ⇛
        x₉}}}}}
      )}}}}}

def expr𝕩𝕩𝕩𝕩₈ : Expr :=
  .lets𝕔 (.lit 1) { 0 ⇛
  .lets𝕔 (.alloc₁ x₀) { 1 ⇛
  .lam𝕔 { 2 ⇛
    .lets𝕔 (.load₁ x₁) { 3 ⇛
      .code (
        .lets (.binary₁ .mul x₂ x₃) { 4 ⇛
        .lets (.store₁ x₁ x₄) { 5 ⇛
        .lets (.load₁ x₁) { 6 ⇛
        .lets (.binary₁ .mul x₂ x₆) { 7 ⇛
        .lets (.store₁ x₁ x₇) { 8 ⇛
        .lets (.load₁ x₁) { 9 ⇛
        x₉}}}}}}
      )}}}}

def expr𝕩𝕩𝕩𝕩₉ : Expr :=
  .lets𝕔 (.lit 1) { 0 ⇛
  .lets𝕔 (.alloc₁ x₀) { 1 ⇛
  .lam𝕔 { 2 ⇛
      .code (
        .lets (.load₁ x₁) { 3 ⇛
        .lets (.binary₁ .mul x₂ x₃) { 4 ⇛
        .lets (.store₁ x₁ x₄) { 5 ⇛
        .lets (.load₁ x₁) { 6 ⇛
        .lets (.binary₁ .mul x₂ x₆) { 7 ⇛
        .lets (.store₁ x₁ x₇) { 8 ⇛
        .lets (.load₁ x₁) { 9 ⇛
        x₉}}}}}}}
      )}}}

def expr𝕩𝕩𝕩𝕩𝕩₀ : Expr :=
  .lets𝕔 (.lit 1) { 0 ⇛
  .lets𝕔 (.alloc₁ x₀) { 1 ⇛
  .reflect (
    .lam { 2 ⇛
      .lets (.load₁ x₁) { 3 ⇛
      .lets (.binary₁ .mul x₂ x₃) { 4 ⇛
      .lets (.store₁ x₁ x₄) { 5 ⇛
      .lets (.load₁ x₁) { 6 ⇛
      .lets (.binary₁ .mul x₂ x₆) { 7 ⇛
      .lets (.store₁ x₁ x₇) { 8 ⇛
      .lets (.load₁ x₁) { 9 ⇛
      x₉}}}}}}}})}}

def expr𝕩𝕩𝕩𝕩𝕩₁ : Expr :=
  .lets𝕔 (.lit 1) { 0 ⇛
  .lets𝕔 (.alloc₁ x₀) { 1 ⇛
  .lets𝕔 (
    .lam { 2 ⇛
      .lets (.load₁ x₁) { 3 ⇛
      .lets (.binary₁ .mul x₂ x₃) { 4 ⇛
      .lets (.store₁ x₁ x₄) { 5 ⇛
      .lets (.load₁ x₁) { 6 ⇛
      .lets (.binary₁ .mul x₂ x₆) { 7 ⇛
      .lets (.store₁ x₁ x₇) { 8 ⇛
      .lets (.load₁ x₁) { 9 ⇛
      x₉}}}}}}}}) { 10 ⇛
    .code f₀}}}

def expr𝕩𝕩𝕩𝕩𝕩₂ : Expr :=
  .lets𝕔 (.lit 1) { 0 ⇛
  .lets𝕔 (.alloc₁ x₀) { 1 ⇛
  .code (
    .lets (
      .lam { 2 ⇛
        .lets (.load₁ x₁) { 3 ⇛
        .lets (.binary₁ .mul x₂ x₃) { 4 ⇛
        .lets (.store₁ x₁ x₄) { 5 ⇛
        .lets (.load₁ x₁) { 6 ⇛
        .lets (.binary₁ .mul x₂ x₆) { 7 ⇛
        .lets (.store₁ x₁ x₇) { 8 ⇛
        .lets (.load₁ x₁) { 9 ⇛
        x₉}}}}}}}}) { 10 ⇛
      f₀})}}

def expr𝕩𝕩𝕩𝕩𝕩₃ : Expr :=
  .lets𝕔 (.lit 1) { 0 ⇛
  .code (
    .lets (.alloc₁ x₀) { 1 ⇛
    .lets (
      .lam { 2 ⇛
        .lets (.load₁ x₁) { 3 ⇛
        .lets (.binary₁ .mul x₂ x₃) { 4 ⇛
        .lets (.store₁ x₁ x₄) { 5 ⇛
        .lets (.load₁ x₁) { 6 ⇛
        .lets (.binary₁ .mul x₂ x₆) { 7 ⇛
        .lets (.store₁ x₁ x₇) { 8 ⇛
        .lets (.load₁ x₁) { 9 ⇛
        x₉}}}}}}}}) { 10 ⇛
      f₀}})}

def expr𝕩𝕩𝕩𝕩𝕩₄ : Expr :=
  .code (
    .lets (.lit 1) { 0 ⇛
    .lets (.alloc₁ x₀) { 1 ⇛
    .lets (
      .lam { 2 ⇛
        .lets (.load₁ x₁) { 3 ⇛
        .lets (.binary₁ .mul x₂ x₃) { 4 ⇛
        .lets (.store₁ x₁ x₄) { 5 ⇛
        .lets (.load₁ x₁) { 6 ⇛
        .lets (.binary₁ .mul x₂ x₆) { 7 ⇛
        .lets (.store₁ x₁ x₇) { 8 ⇛
        .lets (.load₁ x₁) { 9 ⇛
        x₉}}}}}}}}) { 10 ⇛
      f₀}}})

example : (⟨ϵ, expr₀⟩ ⭢ ⟨ϵ, expr₁⟩) := by
  apply step_lvl.pure (fun X => .lets (.alloc₂ X) _)
  apply ctx𝕄.cons𝔹 (fun X => .lets X _)
  repeat constructor

example : (⟨ϵ, expr₁⟩ ⭢ ⟨ϵ, expr₂⟩) := by
  apply step_lvl.reflect id (fun X => .lets (.alloc₂ X) _)
  apply ctxℙ.hole
  apply ctx𝔼.cons𝔹 (fun X => .lets X _)
  repeat constructor

example : (⟨ϵ, expr₂⟩ ⭢ ⟨ϵ, expr₃⟩) := by
  apply step_lvl.pure
    (fun X =>
      .lets𝕔 (.lit 1) { 0 ⇛
      .lets X _})
  apply ctx𝕄.consℝ (fun X => .lets𝕔 (.lit 1) {0 ↤ 0} X)
  apply ctxℝ.lets𝕔; constructor
  apply ctx𝕄.cons𝔹 (fun X => .lets X _)
  repeat constructor

example : (⟨ϵ, expr₃⟩ ⭢ ⟨ϵ, expr₄⟩) := by
  apply step_lvl.reflect (fun X => .lets𝕔 (.lit 1) {0 ↤ 0} X) (fun X => .lets X _)
  apply ctxℙ.consℚ
  apply ctxℚ.holeℝ
  apply ctxℝ.lets𝕔; constructor
  apply ctx𝔼.cons𝔹 (fun X => .lets X _)
  repeat constructor

example : (⟨ϵ, expr₄⟩ ⭢ ⟨ϵ, expr₅⟩) := by
  apply step_lvl.pure
    (fun X =>
      .lets𝕔 (.lit 1) { 0 ⇛
      .lets𝕔 (.alloc₁ x₀) { 1 ⇛
      X}})
  apply ctx𝕄.consℝ (fun X => .lets𝕔 (.lit 1) {0 ↤ 0} X)
  apply ctxℝ.lets𝕔; constructor
  apply ctx𝕄.consℝ (fun X => .lets𝕔 (.alloc₁ x₀) {0 ↤ 1} X)
  repeat constructor

example : (⟨ϵ, expr₅⟩ ⭢ ⟨ϵ, expr₆⟩) := by
  apply step_lvl.pure
    (fun X =>
      .lets𝕔 (.lit 1) { 0 ⇛
      .lets𝕔 (.alloc₁ x₀) { 1 ⇛
      X}})
  apply ctx𝕄.consℝ (fun X => .lets𝕔 (.lit 1) {0 ↤ 0} X)
  apply ctxℝ.lets𝕔; constructor
  apply ctx𝕄.consℝ (fun X => .lets𝕔 (.alloc₁ x₀) {0 ↤ 1} X)
  repeat constructor

example : (⟨ϵ, expr₆⟩ ⭢ ⟨ϵ, expr₇⟩) := by
  apply step_lvl.pure
    (fun X =>
      .lets𝕔 (.lit 1) { 0 ⇛
      .lets𝕔 (.alloc₁ x₀) { 1 ⇛
      X}})
  apply ctx𝕄.consℝ (fun X => .lets𝕔 (.lit 1) {0 ↤ 0} X)
  apply ctxℝ.lets𝕔; constructor
  apply ctx𝕄.consℝ (fun X => .lets𝕔 (.alloc₁ x₀) {0 ↤ 1} X)
  repeat constructor

example : (⟨ϵ, expr₇⟩ ⭢ ⟨ϵ, expr₈⟩) := by
  apply step_lvl.pure
    (fun X =>
      .lets𝕔 (.lit 1) { 0 ⇛
      .lets𝕔 (.alloc₁ x₀) { 1 ⇛
        .lam𝕔 { 2 ⇛
        .app₁ X _}}})
  apply ctx𝕄.consℝ (fun X => .lets𝕔 (.lit 1) {0 ↤ 0} X)
  apply ctxℝ.lets𝕔; constructor
  apply ctx𝕄.consℝ (fun X => .lets𝕔 (.alloc₁ x₀) {0 ↤ 1} X)
  apply ctxℝ.lets𝕔; constructor
  apply ctx𝕄.consℝ (fun X => .lam𝕔 {0 ↤ 2} X)
  apply ctxℝ.lam𝕔
  apply ctx𝕄.cons𝔹 (fun X => .app₁ X _)
  repeat constructor

example : (⟨ϵ, expr₈⟩ ⭢ ⟨ϵ, expr₉⟩) := by
  apply step_lvl.pure
    (fun X =>
      .lets𝕔 (.lit 1) { 0 ⇛
      .lets𝕔 (.alloc₁ x₀) { 1 ⇛
        .lam𝕔 { 2 ⇛
        .app₁ X _}}})
  apply ctx𝕄.consℝ (fun X => .lets𝕔 (.lit 1) {0 ↤ 0} X)
  apply ctxℝ.lets𝕔; constructor
  apply ctx𝕄.consℝ (fun X => .lets𝕔 (.alloc₁ x₀) {0 ↤ 1} X)
  apply ctxℝ.lets𝕔; constructor
  apply ctx𝕄.consℝ (fun X => .lam𝕔 {0 ↤ 2} X)
  apply ctxℝ.lam𝕔
  apply ctx𝕄.cons𝔹 (fun X => .app₁ X _)
  repeat constructor

example : (⟨ϵ, expr₉⟩ ⭢ ⟨ϵ, expr𝕩₀⟩) := by
  apply step_lvl.pure
    (fun X =>
      .lets𝕔 (.lit 1) { 0 ⇛
      .lets𝕔 (.alloc₁ x₀) { 1 ⇛
        .lam𝕔 { 2 ⇛
        X}}})
  apply ctx𝕄.consℝ (fun X => .lets𝕔 (.lit 1) {0 ↤ 0} X)
  apply ctxℝ.lets𝕔; constructor
  apply ctx𝕄.consℝ (fun X => .lets𝕔 (.alloc₁ x₀) {0 ↤ 1} X)
  apply ctxℝ.lets𝕔; constructor
  apply ctx𝕄.consℝ (fun X => .lam𝕔 {0 ↤ 2} X)
  apply ctxℝ.lam𝕔
  repeat constructor

example : (⟨ϵ, expr𝕩₀⟩ ⭢ ⟨ϵ, expr𝕩₁⟩) := by
  let left : Expr :=
    .lam { 103 ⇛
    .lam { 104 ⇛
      .ifz₁ n (
        .load₂ (.code x₁)) (
        .lets (.store₂ (.code x₁) (.binary₂ .mul (.code x₂) (.load₂ (.code x₁)))) (
        .app₁ f (.binary₁ .sub n (.lit 1))))}}
  apply step_lvl.pure
    (fun X =>
      .lets𝕔 (.lit 1) { 0 ⇛
      .lets𝕔 (.alloc₁ x₀) { 1 ⇛
        .lam𝕔 { 2 ⇛
        .app₁ (.app₁ left X) _}}})
  apply ctx𝕄.consℝ (fun X => .lets𝕔 (.lit 1) {0 ↤ 0} X)
  apply ctxℝ.lets𝕔; constructor
  apply ctx𝕄.consℝ (fun X => .lets𝕔 (.alloc₁ x₀) {0 ↤ 1} X)
  apply ctxℝ.lets𝕔; constructor
  apply ctx𝕄.consℝ (fun X => .lam𝕔 {0 ↤ 2} X)
  apply ctxℝ.lam𝕔
  apply ctx𝕄.cons𝔹 (fun X => .app₁ X _)
  repeat constructor

example : (⟨ϵ, expr𝕩₁⟩ ⭢ ⟨ϵ, expr𝕩₂⟩) := by
  apply step_lvl.pure
    (fun X =>
      .lets𝕔 (.lit 1) { 0 ⇛
      .lets𝕔 (.alloc₁ x₀) { 1 ⇛
        .lam𝕔 { 2 ⇛
        .app₁ X _}}})
  apply ctx𝕄.consℝ (fun X => .lets𝕔 (.lit 1) {0 ↤ 0} X)
  apply ctxℝ.lets𝕔; constructor
  apply ctx𝕄.consℝ (fun X => .lets𝕔 (.alloc₁ x₀) {0 ↤ 1} X)
  apply ctxℝ.lets𝕔; constructor
  apply ctx𝕄.consℝ (fun X => .lam𝕔 {0 ↤ 2} X)
  apply ctxℝ.lam𝕔
  apply ctx𝕄.cons𝔹 (fun X => .app₁ X _)
  repeat constructor

example : (⟨ϵ, expr𝕩₂⟩ ⭢ ⟨ϵ, expr𝕩₃⟩) := by
  apply step_lvl.pure
    (fun X =>
      .lets𝕔 (.lit 1) { 0 ⇛
      .lets𝕔 (.alloc₁ x₀) { 1 ⇛
        .lam𝕔 { 2 ⇛
        X}}})
  apply ctx𝕄.consℝ (fun X => .lets𝕔 (.lit 1) {0 ↤ 0} X)
  apply ctxℝ.lets𝕔; constructor
  apply ctx𝕄.consℝ (fun X => .lets𝕔 (.alloc₁ x₀) {0 ↤ 1} X)
  apply ctxℝ.lets𝕔; constructor
  apply ctx𝕄.consℝ (fun X => .lam𝕔 {0 ↤ 2} X)
  apply ctxℝ.lam𝕔
  repeat constructor

example : (⟨ϵ, expr𝕩₃⟩ ⭢ ⟨ϵ, expr𝕩₄⟩) := by
  apply step_lvl.pure
    (fun X =>
      .lets𝕔 (.lit 1) { 0 ⇛
      .lets𝕔 (.alloc₁ x₀) { 1 ⇛
        .lam𝕔 { 2 ⇛
        X}}})
  apply ctx𝕄.consℝ (fun X => .lets𝕔 (.lit 1) {0 ↤ 0} X)
  apply ctxℝ.lets𝕔; constructor
  apply ctx𝕄.consℝ (fun X => .lets𝕔 (.alloc₁ x₀) {0 ↤ 1} X)
  apply ctxℝ.lets𝕔; constructor
  apply ctx𝕄.consℝ (fun X => .lam𝕔 {0 ↤ 2} X)
  apply ctxℝ.lam𝕔
  repeat constructor

example : (⟨ϵ, expr𝕩₄⟩ ⭢ ⟨ϵ, expr𝕩₅⟩) := by
  apply step_lvl.pure
    (fun X =>
      .lets𝕔 (.lit 1) { 0 ⇛
      .lets𝕔 (.alloc₁ x₀) { 1 ⇛
        .lam𝕔 { 2 ⇛
        .lets (.store₂ (.code x₁) (.binary₂ .mul (.code x₂) X)) _}}})
  apply ctx𝕄.consℝ (fun X => .lets𝕔 (.lit 1) {0 ↤ 0} X)
  apply ctxℝ.lets𝕔; constructor
  apply ctx𝕄.consℝ (fun X => .lets𝕔 (.alloc₁ x₀) {0 ↤ 1} X)
  apply ctxℝ.lets𝕔; constructor
  apply ctx𝕄.consℝ (fun X => .lam𝕔 {0 ↤ 2} X)
  apply ctxℝ.lam𝕔
  apply ctx𝕄.cons𝔹 (fun X => .lets X _)
  repeat constructor

example : (⟨ϵ, expr𝕩₅⟩ ⭢ ⟨ϵ, expr𝕩₆⟩) := by
  apply step_lvl.reflect
    (fun X =>
      .lets𝕔 (.lit 1) { 0 ⇛
      .lets𝕔 (.alloc₁ x₀) { 1 ⇛
        .lam𝕔 { 2 ⇛
        X}}})
    (fun X => .lets (.store₂ (.code x₁) (.binary₂ .mul (.code x₂) X)) _)
  apply ctxℙ.consℚ
  apply ctxℚ.consℝ (fun X => .lets𝕔 (.lit 1) {0 ↤ 0} X)
  apply ctxℝ.lets𝕔; constructor
  apply ctxℚ.consℝ (fun X => .lets𝕔 (.alloc₁ x₀) {0 ↤ 1} X)
  apply ctxℝ.lets𝕔; constructor
  apply ctxℚ.holeℝ (fun X => .lam𝕔 {0 ↤ 2} X)
  apply ctxℝ.lam𝕔
  apply ctx𝔼.cons𝔹 (fun X => .lets X _)
  repeat constructor

example : (⟨ϵ, expr𝕩₆⟩ ⭢ ⟨ϵ, expr𝕩₇⟩) := by
  apply step_lvl.pure
    (fun X =>
      .lets𝕔 (.lit 1) { 0 ⇛
      .lets𝕔 (.alloc₁ x₀) { 1 ⇛
        .lam𝕔 { 2 ⇛
          .lets𝕔 (.load₁ x₁) { 3 ⇛
          .lets (.store₂ (.code x₁) X) _}}}})
  apply ctx𝕄.consℝ (fun X => .lets𝕔 (.lit 1) {0 ↤ 0} X)
  apply ctxℝ.lets𝕔; constructor
  apply ctx𝕄.consℝ (fun X => .lets𝕔 (.alloc₁ x₀) {0 ↤ 1} X)
  apply ctxℝ.lets𝕔; constructor
  apply ctx𝕄.consℝ (fun X => .lam𝕔 {0 ↤ 2} X)
  apply ctxℝ.lam𝕔
  apply ctx𝕄.consℝ (fun X => .lets𝕔 (.load₁ x₁) {0 ↤ 3} X)
  apply ctxℝ.lets𝕔; constructor
  apply ctx𝕄.cons𝔹 (fun X => .lets X _)
  repeat constructor

example : (⟨ϵ, expr𝕩₇⟩ ⭢ ⟨ϵ, expr𝕩₈⟩) := by
  apply step_lvl.reflect
    (fun X =>
      .lets𝕔 (.lit 1) { 0 ⇛
      .lets𝕔 (.alloc₁ x₀) { 1 ⇛
        .lam𝕔 { 2 ⇛
          .lets𝕔 (.load₁ x₁) { 3 ⇛
          X}}}})
    (fun X => .lets (.store₂ (.code x₁) X) _)
  apply ctxℙ.consℚ
  apply ctxℚ.consℝ (fun X => .lets𝕔 (.lit 1) {0 ↤ 0} X)
  apply ctxℝ.lets𝕔; constructor
  apply ctxℚ.consℝ (fun X => .lets𝕔 (.alloc₁ x₀) {0 ↤ 1} X)
  apply ctxℝ.lets𝕔; constructor
  apply ctxℚ.consℝ (fun X => .lam𝕔 {0 ↤ 2} X)
  apply ctxℝ.lam𝕔
  apply ctxℚ.holeℝ (fun X => .lets𝕔 (.load₁ x₁) {0 ↤ 3} X)
  apply ctxℝ.lets𝕔; constructor
  apply ctx𝔼.cons𝔹 (fun X => .lets X _)
  repeat constructor

example : (⟨ϵ, expr𝕩₈⟩ ⭢ ⟨ϵ, expr𝕩₉⟩) := by
  apply step_lvl.pure
    (fun X =>
      .lets𝕔 (.lit 1) { 0 ⇛
      .lets𝕔 (.alloc₁ x₀) { 1 ⇛
        .lam𝕔 { 2 ⇛
          .lets𝕔 (.load₁ x₁) { 3 ⇛
          .lets𝕔 (.binary₁ .mul x₂ x₃) { 4 ⇛
          .lets X _}}}}})
  apply ctx𝕄.consℝ (fun X => .lets𝕔 (.lit 1) {0 ↤ 0} X)
  apply ctxℝ.lets𝕔; constructor
  apply ctx𝕄.consℝ (fun X => .lets𝕔 (.alloc₁ x₀) {0 ↤ 1} X)
  apply ctxℝ.lets𝕔; constructor
  apply ctx𝕄.consℝ (fun X => .lam𝕔 {0 ↤ 2} X)
  apply ctxℝ.lam𝕔
  apply ctx𝕄.consℝ (fun X => .lets𝕔 (.load₁ x₁) {0 ↤ 3} X)
  apply ctxℝ.lets𝕔; constructor
  apply ctx𝕄.consℝ (fun X => .lets𝕔 (.binary₁ .mul x₂ x₃) {0 ↤ 4} X)
  apply ctxℝ.lets𝕔; repeat constructor
  apply ctx𝕄.cons𝔹 (fun X => .lets X _)
  repeat constructor

example : (⟨ϵ, expr𝕩₉⟩ ⭢ ⟨ϵ, expr𝕩𝕩₀⟩) := by
  apply step_lvl.reflect
    (fun X =>
      .lets𝕔 (.lit 1) { 0 ⇛
      .lets𝕔 (.alloc₁ x₀) { 1 ⇛
        .lam𝕔 { 2 ⇛
          .lets𝕔 (.load₁ x₁) { 3 ⇛
          .lets𝕔 (.binary₁ .mul x₂ x₃) { 4 ⇛
          X}}}}})
    (fun X => .lets X _)
  apply ctxℙ.consℚ
  apply ctxℚ.consℝ (fun X => .lets𝕔 (.lit 1) {0 ↤ 0} X)
  apply ctxℝ.lets𝕔; constructor
  apply ctxℚ.consℝ (fun X => .lets𝕔 (.alloc₁ x₀) {0 ↤ 1} X)
  apply ctxℝ.lets𝕔; constructor
  apply ctxℚ.consℝ (fun X => .lam𝕔 {0 ↤ 2} X)
  apply ctxℝ.lam𝕔
  apply ctxℚ.consℝ (fun X => .lets𝕔 (.load₁ x₁) {0 ↤ 3} X)
  apply ctxℝ.lets𝕔; constructor
  apply ctxℚ.holeℝ (fun X => .lets𝕔 (.binary₁ .mul x₂ x₃) {0 ↤ 4} X)
  apply ctxℝ.lets𝕔; repeat constructor
  apply ctx𝔼.cons𝔹 (fun X => .lets X _)
  repeat constructor

example : (⟨ϵ, expr𝕩𝕩₀⟩ ⭢ ⟨ϵ, expr𝕩𝕩₁⟩) := by
  apply step_lvl.pure
    (fun X =>
      .lets𝕔 (.lit 1) { 0 ⇛
      .lets𝕔 (.alloc₁ x₀) { 1 ⇛
        .lam𝕔 { 2 ⇛
          .lets𝕔 (.load₁ x₁) { 3 ⇛
          .lets𝕔 (.binary₁ .mul x₂ x₃) { 4 ⇛
          .lets𝕔 (.store₁ x₁ x₄) { 5 ⇛
          X}}}}}})
  apply ctx𝕄.consℝ (fun X => .lets𝕔 (.lit 1) {0 ↤ 0} X)
  apply ctxℝ.lets𝕔; constructor
  apply ctx𝕄.consℝ (fun X => .lets𝕔 (.alloc₁ x₀) {0 ↤ 1} X)
  apply ctxℝ.lets𝕔; constructor
  apply ctx𝕄.consℝ (fun X => .lam𝕔 {0 ↤ 2} X)
  apply ctxℝ.lam𝕔
  apply ctx𝕄.consℝ (fun X => .lets𝕔 (.load₁ x₁) {0 ↤ 3} X)
  apply ctxℝ.lets𝕔; constructor
  apply ctx𝕄.consℝ (fun X => .lets𝕔 (.binary₁ .mul x₂ x₃) {0 ↤ 4} X)
  apply ctxℝ.lets𝕔; constructor; constructor; constructor
  apply ctx𝕄.consℝ (fun X => .lets𝕔 (.store₁ x₁ x₄) {0 ↤ 5} X)
  repeat constructor

example : (⟨ϵ, expr𝕩𝕩₁⟩ ⭢ ⟨ϵ, expr𝕩𝕩₂⟩) := by
  let left : Expr :=
    .lam (
      .app₁ (
        .app₁ (
          .lam { 103 ⇛
          .lam { 104 ⇛
            .ifz₁ n (
              .load₂ (.code x₁)) (
              .lets (.store₂ (.code x₁) (.binary₂ .mul (.code x₂) (.load₂ (.code x₁)))) (
              .app₁ f (.binary₁ .sub n (.lit 1))))}}) (
          .fix₁ (
            .lam { 103 ⇛
            .lam { 104 ⇛
              .ifz₁ n (
                .load₂ (.code x₁)) (
                .lets (.store₂ (.code x₁) (.binary₂ .mul (.code x₂) (.load₂ (.code x₁)))) (
                .app₁ f (.binary₁ .sub n (.lit 1))))}}))) (
        .bvar 0))
  apply step_lvl.pure
    (fun X =>
      .lets𝕔 (.lit 1) { 0 ⇛
      .lets𝕔 (.alloc₁ x₀) { 1 ⇛
        .lam𝕔 { 2 ⇛
          .lets𝕔 (.load₁ x₁) { 3 ⇛
          .lets𝕔 (.binary₁ .mul x₂ x₃) { 4 ⇛
          .lets𝕔 (.store₁ x₁ x₄) { 5 ⇛
          .app₁ left X}}}}}})
  apply ctx𝕄.consℝ (fun X => .lets𝕔 (.lit 1) {0 ↤ 0} X)
  apply ctxℝ.lets𝕔; constructor
  apply ctx𝕄.consℝ (fun X => .lets𝕔 (.alloc₁ x₀) {0 ↤ 1} X)
  apply ctxℝ.lets𝕔; constructor
  apply ctx𝕄.consℝ (fun X => .lam𝕔 {0 ↤ 2} X)
  apply ctxℝ.lam𝕔
  apply ctx𝕄.consℝ (fun X => .lets𝕔 (.load₁ x₁) {0 ↤ 3} X)
  apply ctxℝ.lets𝕔; constructor
  apply ctx𝕄.consℝ (fun X => .lets𝕔 (.binary₁ .mul x₂ x₃) {0 ↤ 4} X)
  apply ctxℝ.lets𝕔; constructor; constructor; constructor
  apply ctx𝕄.consℝ (fun X => .lets𝕔 (.store₁ x₁ x₄) {0 ↤ 5} X)
  repeat constructor

example : (⟨ϵ, expr𝕩𝕩₂⟩ ⭢ ⟨ϵ, expr𝕩𝕩₃⟩) := by
  apply step_lvl.pure
    (fun X =>
      .lets𝕔 (.lit 1) { 0 ⇛
      .lets𝕔 (.alloc₁ x₀) { 1 ⇛
        .lam𝕔 { 2 ⇛
          .lets𝕔 (.load₁ x₁) { 3 ⇛
          .lets𝕔 (.binary₁ .mul x₂ x₃) { 4 ⇛
          .lets𝕔 (.store₁ x₁ x₄) { 5 ⇛
          X}}}}}})
  apply ctx𝕄.consℝ (fun X => .lets𝕔 (.lit 1) {0 ↤ 0} X)
  apply ctxℝ.lets𝕔; constructor
  apply ctx𝕄.consℝ (fun X => .lets𝕔 (.alloc₁ x₀) {0 ↤ 1} X)
  apply ctxℝ.lets𝕔; constructor
  apply ctx𝕄.consℝ (fun X => .lam𝕔 {0 ↤ 2} X)
  apply ctxℝ.lam𝕔
  apply ctx𝕄.consℝ (fun X => .lets𝕔 (.load₁ x₁) {0 ↤ 3} X)
  apply ctxℝ.lets𝕔; constructor
  apply ctx𝕄.consℝ (fun X => .lets𝕔 (.binary₁ .mul x₂ x₃) {0 ↤ 4} X)
  apply ctxℝ.lets𝕔; constructor; constructor; constructor
  apply ctx𝕄.consℝ (fun X => .lets𝕔 (.store₁ x₁ x₄) {0 ↤ 5} X)
  repeat constructor

example : (⟨ϵ, expr𝕩𝕩₃⟩ ⭢ ⟨ϵ, expr𝕩𝕩₄⟩) := by
  let left : Expr :=
    .lam { 103 ⇛
    .lam { 104 ⇛
      .ifz₁ n (
        .load₂ (.code x₁)) (
        .lets (.store₂ (.code x₁) (.binary₂ .mul (.code x₂) (.load₂ (.code x₁)))) (
        .app₁ f (.binary₁ .sub n (.lit 1))))}}
  apply step_lvl.pure
    (fun X =>
      .lets𝕔 (.lit 1) { 0 ⇛
      .lets𝕔 (.alloc₁ x₀) { 1 ⇛
        .lam𝕔 { 2 ⇛
          .lets𝕔 (.load₁ x₁) { 3 ⇛
          .lets𝕔 (.binary₁ .mul x₂ x₃) { 4 ⇛
          .lets𝕔 (.store₁ x₁ x₄) { 5 ⇛
          .app₁ (.app₁ left X) _}}}}}})
  apply ctx𝕄.consℝ (fun X => .lets𝕔 (.lit 1) {0 ↤ 0} X)
  apply ctxℝ.lets𝕔; constructor
  apply ctx𝕄.consℝ (fun X => .lets𝕔 (.alloc₁ x₀) {0 ↤ 1} X)
  apply ctxℝ.lets𝕔; constructor
  apply ctx𝕄.consℝ (fun X => .lam𝕔 {0 ↤ 2} X)
  apply ctxℝ.lam𝕔
  apply ctx𝕄.consℝ (fun X => .lets𝕔 (.load₁ x₁) {0 ↤ 3} X)
  apply ctxℝ.lets𝕔; constructor
  apply ctx𝕄.consℝ (fun X => .lets𝕔 (.binary₁ .mul x₂ x₃) {0 ↤ 4} X)
  apply ctxℝ.lets𝕔; constructor; constructor; constructor
  apply ctx𝕄.consℝ (fun X => .lets𝕔 (.store₁ x₁ x₄) {0 ↤ 5} X)
  apply ctxℝ.lets𝕔; constructor; constructor; constructor
  apply ctx𝕄.cons𝔹 (fun X => .app₁ X _)
  repeat constructor

example : (⟨ϵ, expr𝕩𝕩₄⟩ ⭢ ⟨ϵ, expr𝕩𝕩₅⟩) := by
  apply step_lvl.pure
    (fun X =>
      .lets𝕔 (.lit 1) { 0 ⇛
      .lets𝕔 (.alloc₁ x₀) { 1 ⇛
        .lam𝕔 { 2 ⇛
          .lets𝕔 (.load₁ x₁) { 3 ⇛
          .lets𝕔 (.binary₁ .mul x₂ x₃) { 4 ⇛
          .lets𝕔 (.store₁ x₁ x₄) { 5 ⇛
          .app₁ X _}}}}}})
  apply ctx𝕄.consℝ (fun X => .lets𝕔 (.lit 1) {0 ↤ 0} X)
  apply ctxℝ.lets𝕔; constructor
  apply ctx𝕄.consℝ (fun X => .lets𝕔 (.alloc₁ x₀) {0 ↤ 1} X)
  apply ctxℝ.lets𝕔; constructor
  apply ctx𝕄.consℝ (fun X => .lam𝕔 {0 ↤ 2} X)
  apply ctxℝ.lam𝕔
  apply ctx𝕄.consℝ (fun X => .lets𝕔 (.load₁ x₁) {0 ↤ 3} X)
  apply ctxℝ.lets𝕔; constructor
  apply ctx𝕄.consℝ (fun X => .lets𝕔 (.binary₁ .mul x₂ x₃) {0 ↤ 4} X)
  apply ctxℝ.lets𝕔; constructor; constructor; constructor
  apply ctx𝕄.consℝ (fun X => .lets𝕔 (.store₁ x₁ x₄) {0 ↤ 5} X)
  apply ctxℝ.lets𝕔; constructor; constructor; constructor
  apply ctx𝕄.cons𝔹 (fun X => .app₁ X _)
  repeat constructor

example : (⟨ϵ, expr𝕩𝕩₅⟩ ⭢ ⟨ϵ, expr𝕩𝕩₆⟩) := by
  apply step_lvl.pure
    (fun X =>
      .lets𝕔 (.lit 1) { 0 ⇛
      .lets𝕔 (.alloc₁ x₀) { 1 ⇛
        .lam𝕔 { 2 ⇛
          .lets𝕔 (.load₁ x₁) { 3 ⇛
          .lets𝕔 (.binary₁ .mul x₂ x₃) { 4 ⇛
          .lets𝕔 (.store₁ x₁ x₄) { 5 ⇛
          X}}}}}})
  apply ctx𝕄.consℝ (fun X => .lets𝕔 (.lit 1) {0 ↤ 0} X)
  apply ctxℝ.lets𝕔; constructor
  apply ctx𝕄.consℝ (fun X => .lets𝕔 (.alloc₁ x₀) {0 ↤ 1} X)
  apply ctxℝ.lets𝕔; constructor
  apply ctx𝕄.consℝ (fun X => .lam𝕔 {0 ↤ 2} X)
  apply ctxℝ.lam𝕔
  apply ctx𝕄.consℝ (fun X => .lets𝕔 (.load₁ x₁) {0 ↤ 3} X)
  apply ctxℝ.lets𝕔; constructor
  apply ctx𝕄.consℝ (fun X => .lets𝕔 (.binary₁ .mul x₂ x₃) {0 ↤ 4} X)
  apply ctxℝ.lets𝕔; constructor; constructor; constructor
  apply ctx𝕄.consℝ (fun X => .lets𝕔 (.store₁ x₁ x₄) {0 ↤ 5} X)
  apply ctxℝ.lets𝕔; constructor; constructor; constructor
  repeat constructor

example : (⟨ϵ, expr𝕩𝕩₆⟩ ⭢ ⟨ϵ, expr𝕩𝕩₇⟩) := by
  apply step_lvl.pure
    (fun X =>
      .lets𝕔 (.lit 1) { 0 ⇛
      .lets𝕔 (.alloc₁ x₀) { 1 ⇛
        .lam𝕔 { 2 ⇛
          .lets𝕔 (.load₁ x₁) { 3 ⇛
          .lets𝕔 (.binary₁ .mul x₂ x₃) { 4 ⇛
          .lets𝕔 (.store₁ x₁ x₄) { 5 ⇛
          X}}}}}})
  apply ctx𝕄.consℝ (fun X => .lets𝕔 (.lit 1) {0 ↤ 0} X)
  apply ctxℝ.lets𝕔; constructor
  apply ctx𝕄.consℝ (fun X => .lets𝕔 (.alloc₁ x₀) {0 ↤ 1} X)
  apply ctxℝ.lets𝕔; constructor
  apply ctx𝕄.consℝ (fun X => .lam𝕔 {0 ↤ 2} X)
  apply ctxℝ.lam𝕔
  apply ctx𝕄.consℝ (fun X => .lets𝕔 (.load₁ x₁) {0 ↤ 3} X)
  apply ctxℝ.lets𝕔; constructor
  apply ctx𝕄.consℝ (fun X => .lets𝕔 (.binary₁ .mul x₂ x₃) {0 ↤ 4} X)
  apply ctxℝ.lets𝕔; constructor; constructor; constructor
  apply ctx𝕄.consℝ (fun X => .lets𝕔 (.store₁ x₁ x₄) {0 ↤ 5} X)
  apply ctxℝ.lets𝕔; constructor; constructor; constructor
  repeat constructor

example : (⟨ϵ, expr𝕩𝕩₇⟩ ⭢ ⟨ϵ, expr𝕩𝕩₈⟩) := by
  apply step_lvl.pure
    (fun X =>
      .lets𝕔 (.lit 1) { 0 ⇛
      .lets𝕔 (.alloc₁ x₀) { 1 ⇛
        .lam𝕔 { 2 ⇛
          .lets𝕔 (.load₁ x₁) { 3 ⇛
          .lets𝕔 (.binary₁ .mul x₂ x₃) { 4 ⇛
          .lets𝕔 (.store₁ x₁ x₄) { 5 ⇛
          .lets (.store₂ (.code x₁) (.binary₂ .mul (.code x₂) X)) _}}}}}})
  apply ctx𝕄.consℝ (fun X => .lets𝕔 (.lit 1) {0 ↤ 0} X)
  apply ctxℝ.lets𝕔; constructor
  apply ctx𝕄.consℝ (fun X => .lets𝕔 (.alloc₁ x₀) {0 ↤ 1} X)
  apply ctxℝ.lets𝕔; constructor
  apply ctx𝕄.consℝ (fun X => .lam𝕔 {0 ↤ 2} X)
  apply ctxℝ.lam𝕔
  apply ctx𝕄.consℝ (fun X => .lets𝕔 (.load₁ x₁) {0 ↤ 3} X)
  apply ctxℝ.lets𝕔; constructor
  apply ctx𝕄.consℝ (fun X => .lets𝕔 (.binary₁ .mul x₂ x₃) {0 ↤ 4} X)
  apply ctxℝ.lets𝕔; constructor; constructor; constructor
  apply ctx𝕄.consℝ (fun X => .lets𝕔 (.store₁ x₁ x₄) {0 ↤ 5} X)
  apply ctxℝ.lets𝕔; constructor; constructor; constructor
  apply ctx𝕄.cons𝔹 (fun X => .lets X _)
  repeat constructor

example : (⟨ϵ, expr𝕩𝕩₈⟩ ⭢ ⟨ϵ, expr𝕩𝕩₉⟩) := by
  apply step_lvl.reflect
    (fun X =>
      .lets𝕔 (.lit 1) { 0 ⇛
      .lets𝕔 (.alloc₁ x₀) { 1 ⇛
        .lam𝕔 { 2 ⇛
          .lets𝕔 (.load₁ x₁) { 3 ⇛
          .lets𝕔 (.binary₁ .mul x₂ x₃) { 4 ⇛
          .lets𝕔 (.store₁ x₁ x₄) { 5 ⇛
          X}}}}}})
    (fun X => .lets (.store₂ (.code x₁) (.binary₂ .mul (.code x₂) X)) _)
  apply ctxℙ.consℚ
  apply ctxℚ.consℝ (fun X => .lets𝕔 (.lit 1) {0 ↤ 0} X)
  apply ctxℝ.lets𝕔; constructor
  apply ctxℚ.consℝ (fun X => .lets𝕔 (.alloc₁ x₀) {0 ↤ 1} X)
  apply ctxℝ.lets𝕔; constructor
  apply ctxℚ.consℝ (fun X => .lam𝕔 {0 ↤ 2} X)
  apply ctxℝ.lam𝕔
  apply ctxℚ.consℝ (fun X => .lets𝕔 (.load₁ x₁) {0 ↤ 3} X)
  apply ctxℝ.lets𝕔; constructor
  apply ctxℚ.consℝ (fun X => .lets𝕔 (.binary₁ .mul x₂ x₃) {0 ↤ 4} X)
  apply ctxℝ.lets𝕔; constructor; constructor; constructor
  apply ctxℚ.holeℝ (fun X => .lets𝕔 (.store₁ x₁ x₄) {0 ↤ 5} X)
  apply ctxℝ.lets𝕔; constructor; constructor; constructor
  apply ctx𝔼.cons𝔹 (fun X => .lets X _)
  repeat constructor

example : (⟨ϵ, expr𝕩𝕩₉⟩ ⭢ ⟨ϵ, expr𝕩𝕩𝕩₀⟩) := by
  apply step_lvl.pure
    (fun X =>
      .lets𝕔 (.lit 1) { 0 ⇛
      .lets𝕔 (.alloc₁ x₀) { 1 ⇛
        .lam𝕔 { 2 ⇛
          .lets𝕔 (.load₁ x₁) { 3 ⇛
          .lets𝕔 (.binary₁ .mul x₂ x₃) { 4 ⇛
          .lets𝕔 (.store₁ x₁ x₄) { 5 ⇛
          .lets𝕔 (.load₁ x₁) { 6 ⇛
          .lets (.store₂ (.code x₁) X) _}}}}}}})
  apply ctx𝕄.consℝ (fun X => .lets𝕔 (.lit 1) {0 ↤ 0} X)
  apply ctxℝ.lets𝕔; constructor
  apply ctx𝕄.consℝ (fun X => .lets𝕔 (.alloc₁ x₀) {0 ↤ 1} X)
  apply ctxℝ.lets𝕔; constructor
  apply ctx𝕄.consℝ (fun X => .lam𝕔 {0 ↤ 2} X)
  apply ctxℝ.lam𝕔
  apply ctx𝕄.consℝ (fun X => .lets𝕔 (.load₁ x₁) {0 ↤ 3} X)
  apply ctxℝ.lets𝕔; constructor
  apply ctx𝕄.consℝ (fun X => .lets𝕔 (.binary₁ .mul x₂ x₃) {0 ↤ 4} X)
  apply ctxℝ.lets𝕔; constructor; constructor; constructor
  apply ctx𝕄.consℝ (fun X => .lets𝕔 (.store₁ x₁ x₄) {0 ↤ 5} X)
  apply ctxℝ.lets𝕔; constructor; constructor; constructor
  apply ctx𝕄.consℝ (fun X => .lets𝕔 (.load₁ x₁) {0 ↤ 6} X)
  apply ctxℝ.lets𝕔; constructor
  apply ctx𝕄.cons𝔹 (fun X => .lets X _)
  repeat constructor

example : (⟨ϵ, expr𝕩𝕩𝕩₀⟩ ⭢ ⟨ϵ, expr𝕩𝕩𝕩₁⟩) := by
  apply step_lvl.reflect
    (fun X =>
      .lets𝕔 (.lit 1) { 0 ⇛
      .lets𝕔 (.alloc₁ x₀) { 1 ⇛
        .lam𝕔 { 2 ⇛
          .lets𝕔 (.load₁ x₁) { 3 ⇛
          .lets𝕔 (.binary₁ .mul x₂ x₃) { 4 ⇛
          .lets𝕔 (.store₁ x₁ x₄) { 5 ⇛
          .lets𝕔 (.load₁ x₁) { 6 ⇛
          X}}}}}}})
    (fun X => .lets (.store₂ (.code x₁) X) _)
  apply ctxℙ.consℚ
  apply ctxℚ.consℝ (fun X => .lets𝕔 (.lit 1) {0 ↤ 0} X)
  apply ctxℝ.lets𝕔; constructor
  apply ctxℚ.consℝ (fun X => .lets𝕔 (.alloc₁ x₀) {0 ↤ 1} X)
  apply ctxℝ.lets𝕔; constructor
  apply ctxℚ.consℝ (fun X => .lam𝕔 {0 ↤ 2} X)
  apply ctxℝ.lam𝕔
  apply ctxℚ.consℝ (fun X => .lets𝕔 (.load₁ x₁) {0 ↤ 3} X)
  apply ctxℝ.lets𝕔; constructor
  apply ctxℚ.consℝ (fun X => .lets𝕔 (.binary₁ .mul x₂ x₃) {0 ↤ 4} X)
  apply ctxℝ.lets𝕔; constructor; constructor; constructor
  apply ctxℚ.consℝ (fun X => .lets𝕔 (.store₁ x₁ x₄) {0 ↤ 5} X)
  apply ctxℝ.lets𝕔; constructor; constructor; constructor
  apply ctxℚ.holeℝ (fun X => .lets𝕔 (.load₁ x₁) {0 ↤ 6} X)
  apply ctxℝ.lets𝕔; constructor
  apply ctx𝔼.cons𝔹 (fun X => .lets X _)
  repeat constructor

example : (⟨ϵ, expr𝕩𝕩𝕩₁⟩ ⭢ ⟨ϵ, expr𝕩𝕩𝕩₂⟩) := by
  apply step_lvl.pure
    (fun X =>
      .lets𝕔 (.lit 1) { 0 ⇛
      .lets𝕔 (.alloc₁ x₀) { 1 ⇛
        .lam𝕔 { 2 ⇛
          .lets𝕔 (.load₁ x₁) { 3 ⇛
          .lets𝕔 (.binary₁ .mul x₂ x₃) { 4 ⇛
          .lets𝕔 (.store₁ x₁ x₄) { 5 ⇛
          .lets𝕔 (.load₁ x₁) { 6 ⇛
          .lets𝕔 (.binary₁ .mul x₂ x₆) { 7 ⇛
          .lets X _}}}}}}}})
  apply ctx𝕄.consℝ (fun X => .lets𝕔 (.lit 1) {0 ↤ 0} X)
  apply ctxℝ.lets𝕔; constructor
  apply ctx𝕄.consℝ (fun X => .lets𝕔 (.alloc₁ x₀) {0 ↤ 1} X)
  apply ctxℝ.lets𝕔; constructor
  apply ctx𝕄.consℝ (fun X => .lam𝕔 {0 ↤ 2} X)
  apply ctxℝ.lam𝕔
  apply ctx𝕄.consℝ (fun X => .lets𝕔 (.load₁ x₁) {0 ↤ 3} X)
  apply ctxℝ.lets𝕔; constructor
  apply ctx𝕄.consℝ (fun X => .lets𝕔 (.binary₁ .mul x₂ x₃) {0 ↤ 4} X)
  apply ctxℝ.lets𝕔; constructor; constructor; constructor
  apply ctx𝕄.consℝ (fun X => .lets𝕔 (.store₁ x₁ x₄) {0 ↤ 5} X)
  apply ctxℝ.lets𝕔; constructor; constructor; constructor
  apply ctx𝕄.consℝ (fun X => .lets𝕔 (.load₁ x₁) {0 ↤ 6} X)
  apply ctxℝ.lets𝕔; constructor
  apply ctx𝕄.consℝ (fun X => .lets𝕔 (.binary₁ .mul x₂ x₆) {0 ↤ 7} X)
  apply ctxℝ.lets𝕔; constructor; constructor; constructor
  apply ctx𝕄.cons𝔹 (fun X => .lets X _)
  repeat constructor

example : (⟨ϵ, expr𝕩𝕩𝕩₂⟩ ⭢ ⟨ϵ, expr𝕩𝕩𝕩₃⟩) := by
  apply step_lvl.reflect
    (fun X =>
      .lets𝕔 (.lit 1) { 0 ⇛
      .lets𝕔 (.alloc₁ x₀) { 1 ⇛
        .lam𝕔 { 2 ⇛
          .lets𝕔 (.load₁ x₁) { 3 ⇛
          .lets𝕔 (.binary₁ .mul x₂ x₃) { 4 ⇛
          .lets𝕔 (.store₁ x₁ x₄) { 5 ⇛
          .lets𝕔 (.load₁ x₁) { 6 ⇛
          .lets𝕔 (.binary₁ .mul x₂ x₆) { 7 ⇛
          X}}}}}}}})
    (fun X => .lets X _)
  apply ctxℙ.consℚ
  apply ctxℚ.consℝ (fun X => .lets𝕔 (.lit 1) {0 ↤ 0} X)
  apply ctxℝ.lets𝕔; constructor
  apply ctxℚ.consℝ (fun X => .lets𝕔 (.alloc₁ x₀) {0 ↤ 1} X)
  apply ctxℝ.lets𝕔; constructor
  apply ctxℚ.consℝ (fun X => .lam𝕔 {0 ↤ 2} X)
  apply ctxℝ.lam𝕔
  apply ctxℚ.consℝ (fun X => .lets𝕔 (.load₁ x₁) {0 ↤ 3} X)
  apply ctxℝ.lets𝕔; constructor
  apply ctxℚ.consℝ (fun X => .lets𝕔 (.binary₁ .mul x₂ x₃) {0 ↤ 4} X)
  apply ctxℝ.lets𝕔; constructor; constructor; constructor
  apply ctxℚ.consℝ (fun X => .lets𝕔 (.store₁ x₁ x₄) {0 ↤ 5} X)
  apply ctxℝ.lets𝕔; constructor; constructor; constructor
  apply ctxℚ.consℝ (fun X => .lets𝕔 (.load₁ x₁) {0 ↤ 6} X)
  apply ctxℝ.lets𝕔; constructor
  apply ctxℚ.holeℝ (fun X => .lets𝕔 (.binary₁ .mul x₂ x₆) {0 ↤ 7} X)
  apply ctxℝ.lets𝕔; constructor; constructor; constructor
  apply ctx𝔼.cons𝔹 (fun X => .lets X _)
  repeat constructor

example : (⟨ϵ, expr𝕩𝕩𝕩₃⟩ ⭢ ⟨ϵ, expr𝕩𝕩𝕩₄⟩) := by
  apply step_lvl.pure
    (fun X =>
      .lets𝕔 (.lit 1) { 0 ⇛
      .lets𝕔 (.alloc₁ x₀) { 1 ⇛
        .lam𝕔 { 2 ⇛
          .lets𝕔 (.load₁ x₁) { 3 ⇛
          .lets𝕔 (.binary₁ .mul x₂ x₃) { 4 ⇛
          .lets𝕔 (.store₁ x₁ x₄) { 5 ⇛
          .lets𝕔 (.load₁ x₁) { 6 ⇛
          .lets𝕔 (.binary₁ .mul x₂ x₆) { 7 ⇛
          .lets𝕔 (.store₁ x₁ x₇) { 8 ⇛
          X}}}}}}}}})
  apply ctx𝕄.consℝ (fun X => .lets𝕔 (.lit 1) {0 ↤ 0} X)
  apply ctxℝ.lets𝕔; constructor
  apply ctx𝕄.consℝ (fun X => .lets𝕔 (.alloc₁ x₀) {0 ↤ 1} X)
  apply ctxℝ.lets𝕔; constructor
  apply ctx𝕄.consℝ (fun X => .lam𝕔 {0 ↤ 2} X)
  apply ctxℝ.lam𝕔
  apply ctx𝕄.consℝ (fun X => .lets𝕔 (.load₁ x₁) {0 ↤ 3} X)
  apply ctxℝ.lets𝕔; constructor
  apply ctx𝕄.consℝ (fun X => .lets𝕔 (.binary₁ .mul x₂ x₃) {0 ↤ 4} X)
  apply ctxℝ.lets𝕔; constructor; constructor; constructor
  apply ctx𝕄.consℝ (fun X => .lets𝕔 (.store₁ x₁ x₄) {0 ↤ 5} X)
  apply ctxℝ.lets𝕔; constructor; constructor; constructor
  apply ctx𝕄.consℝ (fun X => .lets𝕔 (.load₁ x₁) {0 ↤ 6} X)
  apply ctxℝ.lets𝕔; constructor
  apply ctx𝕄.consℝ (fun X => .lets𝕔 (.binary₁ .mul x₂ x₆) {0 ↤ 7} X)
  apply ctxℝ.lets𝕔; constructor; constructor; constructor
  apply ctx𝕄.consℝ (fun X => .lets𝕔 (.store₁ x₁ x₇) {0 ↤ 8} X)
  apply ctxℝ.lets𝕔; constructor; constructor; constructor
  repeat constructor

example : (⟨ϵ, expr𝕩𝕩𝕩₄⟩ ⭢ ⟨ϵ, expr𝕩𝕩𝕩₅⟩) := by
  let left : Expr :=
    .lam (
      .app₁ (
        .app₁ (
          .lam { 103 ⇛
          .lam { 104 ⇛
            .ifz₁ n (
              .load₂ (.code x₁)) (
              .lets (.store₂ (.code x₁) (.binary₂ .mul (.code x₂) (.load₂ (.code x₁)))) (
              .app₁ f (.binary₁ .sub n (.lit 1))))}}) (
          .fix₁ (
            .lam { 103 ⇛
            .lam { 104 ⇛
              .ifz₁ n (
                .load₂ (.code x₁)) (
                .lets (.store₂ (.code x₁) (.binary₂ .mul (.code x₂) (.load₂ (.code x₁)))) (
                .app₁ f (.binary₁ .sub n (.lit 1))))}}))) (
        .bvar 0))
  apply step_lvl.pure
    (fun X =>
      .lets𝕔 (.lit 1) { 0 ⇛
      .lets𝕔 (.alloc₁ x₀) { 1 ⇛
        .lam𝕔 { 2 ⇛
          .lets𝕔 (.load₁ x₁) { 3 ⇛
          .lets𝕔 (.binary₁ .mul x₂ x₃) { 4 ⇛
          .lets𝕔 (.store₁ x₁ x₄) { 5 ⇛
          .lets𝕔 (.load₁ x₁) { 6 ⇛
          .lets𝕔 (.binary₁ .mul x₂ x₆) { 7 ⇛
          .lets𝕔 (.store₁ x₁ x₇) { 8 ⇛
          .app₁ left X}}}}}}}}})
  apply ctx𝕄.consℝ (fun X => .lets𝕔 (.lit 1) {0 ↤ 0} X)
  apply ctxℝ.lets𝕔; constructor
  apply ctx𝕄.consℝ (fun X => .lets𝕔 (.alloc₁ x₀) {0 ↤ 1} X)
  apply ctxℝ.lets𝕔; constructor
  apply ctx𝕄.consℝ (fun X => .lam𝕔 {0 ↤ 2} X)
  apply ctxℝ.lam𝕔
  apply ctx𝕄.consℝ (fun X => .lets𝕔 (.load₁ x₁) {0 ↤ 3} X)
  apply ctxℝ.lets𝕔; constructor
  apply ctx𝕄.consℝ (fun X => .lets𝕔 (.binary₁ .mul x₂ x₃) {0 ↤ 4} X)
  apply ctxℝ.lets𝕔; constructor; constructor; constructor
  apply ctx𝕄.consℝ (fun X => .lets𝕔 (.store₁ x₁ x₄) {0 ↤ 5} X)
  apply ctxℝ.lets𝕔; constructor; constructor; constructor
  apply ctx𝕄.consℝ (fun X => .lets𝕔 (.load₁ x₁) {0 ↤ 6} X)
  apply ctxℝ.lets𝕔; constructor
  apply ctx𝕄.consℝ (fun X => .lets𝕔 (.binary₁ .mul x₂ x₆) {0 ↤ 7} X)
  apply ctxℝ.lets𝕔; constructor; constructor; constructor
  apply ctx𝕄.consℝ (fun X => .lets𝕔 (.store₁ x₁ x₇) {0 ↤ 8} X)
  apply ctxℝ.lets𝕔; constructor; constructor; constructor
  repeat constructor

example : (⟨ϵ, expr𝕩𝕩𝕩₅⟩ ⭢ ⟨ϵ, expr𝕩𝕩𝕩₆⟩) := by
  apply step_lvl.pure
    (fun X =>
      .lets𝕔 (.lit 1) { 0 ⇛
      .lets𝕔 (.alloc₁ x₀) { 1 ⇛
        .lam𝕔 { 2 ⇛
          .lets𝕔 (.load₁ x₁) { 3 ⇛
          .lets𝕔 (.binary₁ .mul x₂ x₃) { 4 ⇛
          .lets𝕔 (.store₁ x₁ x₄) { 5 ⇛
          .lets𝕔 (.load₁ x₁) { 6 ⇛
          .lets𝕔 (.binary₁ .mul x₂ x₆) { 7 ⇛
          .lets𝕔 (.store₁ x₁ x₇) { 8 ⇛
          X}}}}}}}}})
  apply ctx𝕄.consℝ (fun X => .lets𝕔 (.lit 1) {0 ↤ 0} X)
  apply ctxℝ.lets𝕔; constructor
  apply ctx𝕄.consℝ (fun X => .lets𝕔 (.alloc₁ x₀) {0 ↤ 1} X)
  apply ctxℝ.lets𝕔; constructor
  apply ctx𝕄.consℝ (fun X => .lam𝕔 {0 ↤ 2} X)
  apply ctxℝ.lam𝕔
  apply ctx𝕄.consℝ (fun X => .lets𝕔 (.load₁ x₁) {0 ↤ 3} X)
  apply ctxℝ.lets𝕔; constructor
  apply ctx𝕄.consℝ (fun X => .lets𝕔 (.binary₁ .mul x₂ x₃) {0 ↤ 4} X)
  apply ctxℝ.lets𝕔; constructor; constructor; constructor
  apply ctx𝕄.consℝ (fun X => .lets𝕔 (.store₁ x₁ x₄) {0 ↤ 5} X)
  apply ctxℝ.lets𝕔; constructor; constructor; constructor
  apply ctx𝕄.consℝ (fun X => .lets𝕔 (.load₁ x₁) {0 ↤ 6} X)
  apply ctxℝ.lets𝕔; constructor
  apply ctx𝕄.consℝ (fun X => .lets𝕔 (.binary₁ .mul x₂ x₆) {0 ↤ 7} X)
  apply ctxℝ.lets𝕔; constructor; constructor; constructor
  apply ctx𝕄.consℝ (fun X => .lets𝕔 (.store₁ x₁ x₇) {0 ↤ 8} X)
  apply ctxℝ.lets𝕔; constructor; constructor; constructor
  repeat constructor

example : (⟨ϵ, expr𝕩𝕩𝕩₆⟩ ⭢ ⟨ϵ, expr𝕩𝕩𝕩₇⟩) := by
  let left : Expr :=
    .lam { 103 ⇛
    .lam { 104 ⇛
      .ifz₁ n (
        .load₂ (.code x₁)) (
        .lets (.store₂ (.code x₁) (.binary₂ .mul (.code x₂) (.load₂ (.code x₁)))) (
        .app₁ f (.binary₁ .sub n (.lit 1))))}}
  apply step_lvl.pure
    (fun X =>
      .lets𝕔 (.lit 1) { 0 ⇛
      .lets𝕔 (.alloc₁ x₀) { 1 ⇛
        .lam𝕔 { 2 ⇛
          .lets𝕔 (.load₁ x₁) { 3 ⇛
          .lets𝕔 (.binary₁ .mul x₂ x₃) { 4 ⇛
          .lets𝕔 (.store₁ x₁ x₄) { 5 ⇛
          .lets𝕔 (.load₁ x₁) { 6 ⇛
          .lets𝕔 (.binary₁ .mul x₂ x₆) { 7 ⇛
          .lets𝕔 (.store₁ x₁ x₇) { 8 ⇛
          .app₁ (.app₁ left X) _}}}}}}}}})
  apply ctx𝕄.consℝ (fun X => .lets𝕔 (.lit 1) {0 ↤ 0} X)
  apply ctxℝ.lets𝕔; constructor
  apply ctx𝕄.consℝ (fun X => .lets𝕔 (.alloc₁ x₀) {0 ↤ 1} X)
  apply ctxℝ.lets𝕔; constructor
  apply ctx𝕄.consℝ (fun X => .lam𝕔 {0 ↤ 2} X)
  apply ctxℝ.lam𝕔
  apply ctx𝕄.consℝ (fun X => .lets𝕔 (.load₁ x₁) {0 ↤ 3} X)
  apply ctxℝ.lets𝕔; constructor
  apply ctx𝕄.consℝ (fun X => .lets𝕔 (.binary₁ .mul x₂ x₃) {0 ↤ 4} X)
  apply ctxℝ.lets𝕔; constructor; constructor; constructor
  apply ctx𝕄.consℝ (fun X => .lets𝕔 (.store₁ x₁ x₄) {0 ↤ 5} X)
  apply ctxℝ.lets𝕔; constructor; constructor; constructor
  apply ctx𝕄.consℝ (fun X => .lets𝕔 (.load₁ x₁) {0 ↤ 6} X)
  apply ctxℝ.lets𝕔; constructor
  apply ctx𝕄.consℝ (fun X => .lets𝕔 (.binary₁ .mul x₂ x₆) {0 ↤ 7} X)
  apply ctxℝ.lets𝕔; constructor; constructor; constructor
  apply ctx𝕄.consℝ (fun X => .lets𝕔 (.store₁ x₁ x₇) {0 ↤ 8} X)
  apply ctxℝ.lets𝕔; constructor; constructor; constructor
  apply ctx𝕄.cons𝔹 (fun X => .app₁ X _)
  repeat constructor

example : (⟨ϵ, expr𝕩𝕩𝕩₇⟩ ⭢ ⟨ϵ, expr𝕩𝕩𝕩₈⟩) := by
  apply step_lvl.pure
    (fun X =>
      .lets𝕔 (.lit 1) { 0 ⇛
      .lets𝕔 (.alloc₁ x₀) { 1 ⇛
        .lam𝕔 { 2 ⇛
          .lets𝕔 (.load₁ x₁) { 3 ⇛
          .lets𝕔 (.binary₁ .mul x₂ x₃) { 4 ⇛
          .lets𝕔 (.store₁ x₁ x₄) { 5 ⇛
          .lets𝕔 (.load₁ x₁) { 6 ⇛
          .lets𝕔 (.binary₁ .mul x₂ x₆) { 7 ⇛
          .lets𝕔 (.store₁ x₁ x₇) { 8 ⇛
          .app₁ X _}}}}}}}}})
  apply ctx𝕄.consℝ (fun X => .lets𝕔 (.lit 1) {0 ↤ 0} X)
  apply ctxℝ.lets𝕔; constructor
  apply ctx𝕄.consℝ (fun X => .lets𝕔 (.alloc₁ x₀) {0 ↤ 1} X)
  apply ctxℝ.lets𝕔; constructor
  apply ctx𝕄.consℝ (fun X => .lam𝕔 {0 ↤ 2} X)
  apply ctxℝ.lam𝕔
  apply ctx𝕄.consℝ (fun X => .lets𝕔 (.load₁ x₁) {0 ↤ 3} X)
  apply ctxℝ.lets𝕔; constructor
  apply ctx𝕄.consℝ (fun X => .lets𝕔 (.binary₁ .mul x₂ x₃) {0 ↤ 4} X)
  apply ctxℝ.lets𝕔; constructor; constructor; constructor
  apply ctx𝕄.consℝ (fun X => .lets𝕔 (.store₁ x₁ x₄) {0 ↤ 5} X)
  apply ctxℝ.lets𝕔; constructor; constructor; constructor
  apply ctx𝕄.consℝ (fun X => .lets𝕔 (.load₁ x₁) {0 ↤ 6} X)
  apply ctxℝ.lets𝕔; constructor
  apply ctx𝕄.consℝ (fun X => .lets𝕔 (.binary₁ .mul x₂ x₆) {0 ↤ 7} X)
  apply ctxℝ.lets𝕔; constructor; constructor; constructor
  apply ctx𝕄.consℝ (fun X => .lets𝕔 (.store₁ x₁ x₇) {0 ↤ 8} X)
  apply ctxℝ.lets𝕔; constructor; constructor; constructor
  apply ctx𝕄.cons𝔹 (fun X => .app₁ X _)
  repeat constructor

example : (⟨ϵ, expr𝕩𝕩𝕩₈⟩ ⭢ ⟨ϵ, expr𝕩𝕩𝕩₉⟩) := by
  apply step_lvl.pure
    (fun X =>
      .lets𝕔 (.lit 1) { 0 ⇛
      .lets𝕔 (.alloc₁ x₀) { 1 ⇛
        .lam𝕔 { 2 ⇛
          .lets𝕔 (.load₁ x₁) { 3 ⇛
          .lets𝕔 (.binary₁ .mul x₂ x₃) { 4 ⇛
          .lets𝕔 (.store₁ x₁ x₄) { 5 ⇛
          .lets𝕔 (.load₁ x₁) { 6 ⇛
          .lets𝕔 (.binary₁ .mul x₂ x₆) { 7 ⇛
          .lets𝕔 (.store₁ x₁ x₇) { 8 ⇛
          X}}}}}}}}})
  apply ctx𝕄.consℝ (fun X => .lets𝕔 (.lit 1) {0 ↤ 0} X)
  apply ctxℝ.lets𝕔; constructor
  apply ctx𝕄.consℝ (fun X => .lets𝕔 (.alloc₁ x₀) {0 ↤ 1} X)
  apply ctxℝ.lets𝕔; constructor
  apply ctx𝕄.consℝ (fun X => .lam𝕔 {0 ↤ 2} X)
  apply ctxℝ.lam𝕔
  apply ctx𝕄.consℝ (fun X => .lets𝕔 (.load₁ x₁) {0 ↤ 3} X)
  apply ctxℝ.lets𝕔; constructor
  apply ctx𝕄.consℝ (fun X => .lets𝕔 (.binary₁ .mul x₂ x₃) {0 ↤ 4} X)
  apply ctxℝ.lets𝕔; constructor; constructor; constructor
  apply ctx𝕄.consℝ (fun X => .lets𝕔 (.store₁ x₁ x₄) {0 ↤ 5} X)
  apply ctxℝ.lets𝕔; constructor; constructor; constructor
  apply ctx𝕄.consℝ (fun X => .lets𝕔 (.load₁ x₁) {0 ↤ 6} X)
  apply ctxℝ.lets𝕔; constructor
  apply ctx𝕄.consℝ (fun X => .lets𝕔 (.binary₁ .mul x₂ x₆) {0 ↤ 7} X)
  apply ctxℝ.lets𝕔; constructor; constructor; constructor
  apply ctx𝕄.consℝ (fun X => .lets𝕔 (.store₁ x₁ x₇) {0 ↤ 8} X)
  apply ctxℝ.lets𝕔; constructor; constructor; constructor
  repeat constructor

example : (⟨ϵ, expr𝕩𝕩𝕩₉⟩ ⭢ ⟨ϵ, expr𝕩𝕩𝕩𝕩₀⟩) := by
  apply step_lvl.pure
    (fun X =>
      .lets𝕔 (.lit 1) { 0 ⇛
      .lets𝕔 (.alloc₁ x₀) { 1 ⇛
        .lam𝕔 { 2 ⇛
          .lets𝕔 (.load₁ x₁) { 3 ⇛
          .lets𝕔 (.binary₁ .mul x₂ x₃) { 4 ⇛
          .lets𝕔 (.store₁ x₁ x₄) { 5 ⇛
          .lets𝕔 (.load₁ x₁) { 6 ⇛
          .lets𝕔 (.binary₁ .mul x₂ x₆) { 7 ⇛
          .lets𝕔 (.store₁ x₁ x₇) { 8 ⇛
          X}}}}}}}}})
  apply ctx𝕄.consℝ (fun X => .lets𝕔 (.lit 1) {0 ↤ 0} X)
  apply ctxℝ.lets𝕔; constructor
  apply ctx𝕄.consℝ (fun X => .lets𝕔 (.alloc₁ x₀) {0 ↤ 1} X)
  apply ctxℝ.lets𝕔; constructor
  apply ctx𝕄.consℝ (fun X => .lam𝕔 {0 ↤ 2} X)
  apply ctxℝ.lam𝕔
  apply ctx𝕄.consℝ (fun X => .lets𝕔 (.load₁ x₁) {0 ↤ 3} X)
  apply ctxℝ.lets𝕔; constructor
  apply ctx𝕄.consℝ (fun X => .lets𝕔 (.binary₁ .mul x₂ x₃) {0 ↤ 4} X)
  apply ctxℝ.lets𝕔; constructor; constructor; constructor
  apply ctx𝕄.consℝ (fun X => .lets𝕔 (.store₁ x₁ x₄) {0 ↤ 5} X)
  apply ctxℝ.lets𝕔; constructor; constructor; constructor
  apply ctx𝕄.consℝ (fun X => .lets𝕔 (.load₁ x₁) {0 ↤ 6} X)
  apply ctxℝ.lets𝕔; constructor
  apply ctx𝕄.consℝ (fun X => .lets𝕔 (.binary₁ .mul x₂ x₆) {0 ↤ 7} X)
  apply ctxℝ.lets𝕔; constructor; constructor; constructor
  apply ctx𝕄.consℝ (fun X => .lets𝕔 (.store₁ x₁ x₇) {0 ↤ 8} X)
  apply ctxℝ.lets𝕔; constructor; constructor; constructor
  repeat constructor

example : (⟨ϵ, expr𝕩𝕩𝕩𝕩₀⟩ ⭢ ⟨ϵ, expr𝕩𝕩𝕩𝕩₁⟩) := by
  apply step_lvl.pure
    (fun X =>
      .lets𝕔 (.lit 1) { 0 ⇛
      .lets𝕔 (.alloc₁ x₀) { 1 ⇛
        .lam𝕔 { 2 ⇛
          .lets𝕔 (.load₁ x₁) { 3 ⇛
          .lets𝕔 (.binary₁ .mul x₂ x₃) { 4 ⇛
          .lets𝕔 (.store₁ x₁ x₄) { 5 ⇛
          .lets𝕔 (.load₁ x₁) { 6 ⇛
          .lets𝕔 (.binary₁ .mul x₂ x₆) { 7 ⇛
          .lets𝕔 (.store₁ x₁ x₇) { 8 ⇛
          X}}}}}}}}})
  apply ctx𝕄.consℝ (fun X => .lets𝕔 (.lit 1) {0 ↤ 0} X)
  apply ctxℝ.lets𝕔; constructor
  apply ctx𝕄.consℝ (fun X => .lets𝕔 (.alloc₁ x₀) {0 ↤ 1} X)
  apply ctxℝ.lets𝕔; constructor
  apply ctx𝕄.consℝ (fun X => .lam𝕔 {0 ↤ 2} X)
  apply ctxℝ.lam𝕔
  apply ctx𝕄.consℝ (fun X => .lets𝕔 (.load₁ x₁) {0 ↤ 3} X)
  apply ctxℝ.lets𝕔; constructor
  apply ctx𝕄.consℝ (fun X => .lets𝕔 (.binary₁ .mul x₂ x₃) {0 ↤ 4} X)
  apply ctxℝ.lets𝕔; constructor; constructor; constructor
  apply ctx𝕄.consℝ (fun X => .lets𝕔 (.store₁ x₁ x₄) {0 ↤ 5} X)
  apply ctxℝ.lets𝕔; constructor; constructor; constructor
  apply ctx𝕄.consℝ (fun X => .lets𝕔 (.load₁ x₁) {0 ↤ 6} X)
  apply ctxℝ.lets𝕔; constructor
  apply ctx𝕄.consℝ (fun X => .lets𝕔 (.binary₁ .mul x₂ x₆) {0 ↤ 7} X)
  apply ctxℝ.lets𝕔; constructor; constructor; constructor
  apply ctx𝕄.consℝ (fun X => .lets𝕔 (.store₁ x₁ x₇) {0 ↤ 8} X)
  apply ctxℝ.lets𝕔; constructor; constructor; constructor
  repeat constructor

example : (⟨ϵ, expr𝕩𝕩𝕩𝕩₁⟩ ⭢ ⟨ϵ, expr𝕩𝕩𝕩𝕩₂⟩) := by
  apply step_lvl.reflect
    (fun X =>
      .lets𝕔 (.lit 1) { 0 ⇛
      .lets𝕔 (.alloc₁ x₀) { 1 ⇛
        .lam𝕔 { 2 ⇛
          .lets𝕔 (.load₁ x₁) { 3 ⇛
          .lets𝕔 (.binary₁ .mul x₂ x₃) { 4 ⇛
          .lets𝕔 (.store₁ x₁ x₄) { 5 ⇛
          .lets𝕔 (.load₁ x₁) { 6 ⇛
          .lets𝕔 (.binary₁ .mul x₂ x₆) { 7 ⇛
          .lets𝕔 (.store₁ x₁ x₇) { 8 ⇛
          X}}}}}}}}})
    id
  apply ctxℙ.consℚ
  apply ctxℚ.consℝ (fun X => .lets𝕔 (.lit 1) {0 ↤ 0} X)
  apply ctxℝ.lets𝕔; constructor
  apply ctxℚ.consℝ (fun X => .lets𝕔 (.alloc₁ x₀) {0 ↤ 1} X)
  apply ctxℝ.lets𝕔; constructor
  apply ctxℚ.consℝ (fun X => .lam𝕔 {0 ↤ 2} X)
  apply ctxℝ.lam𝕔
  apply ctxℚ.consℝ (fun X => .lets𝕔 (.load₁ x₁) {0 ↤ 3} X)
  apply ctxℝ.lets𝕔; constructor
  apply ctxℚ.consℝ (fun X => .lets𝕔 (.binary₁ .mul x₂ x₃) {0 ↤ 4} X)
  apply ctxℝ.lets𝕔; constructor; constructor; constructor
  apply ctxℚ.consℝ (fun X => .lets𝕔 (.store₁ x₁ x₄) {0 ↤ 5} X)
  apply ctxℝ.lets𝕔; constructor; constructor; constructor
  apply ctxℚ.consℝ (fun X => .lets𝕔 (.load₁ x₁) {0 ↤ 6} X)
  apply ctxℝ.lets𝕔; constructor
  apply ctxℚ.consℝ (fun X => .lets𝕔 (.binary₁ .mul x₂ x₆) {0 ↤ 7} X)
  apply ctxℝ.lets𝕔; constructor; constructor; constructor
  apply ctxℚ.holeℝ (fun X => .lets𝕔 (.store₁ x₁ x₇) {0 ↤ 8} X)
  apply ctxℝ.lets𝕔; constructor; constructor; constructor
  repeat constructor

example : (⟨ϵ, expr𝕩𝕩𝕩𝕩₂⟩ ⭢ ⟨ϵ, expr𝕩𝕩𝕩𝕩₃⟩) := by
  apply step_lvl.pure
    (fun X =>
      .lets𝕔 (.lit 1) { 0 ⇛
      .lets𝕔 (.alloc₁ x₀) { 1 ⇛
        .lam𝕔 { 2 ⇛
          .lets𝕔 (.load₁ x₁) { 3 ⇛
          .lets𝕔 (.binary₁ .mul x₂ x₃) { 4 ⇛
          .lets𝕔 (.store₁ x₁ x₄) { 5 ⇛
          .lets𝕔 (.load₁ x₁) { 6 ⇛
          .lets𝕔 (.binary₁ .mul x₂ x₆) { 7 ⇛
          .lets𝕔 (.store₁ x₁ x₇) { 8 ⇛
          X}}}}}}}}})
  apply ctx𝕄.consℝ (fun X => .lets𝕔 (.lit 1) {0 ↤ 0} X)
  apply ctxℝ.lets𝕔; constructor
  apply ctx𝕄.consℝ (fun X => .lets𝕔 (.alloc₁ x₀) {0 ↤ 1} X)
  apply ctxℝ.lets𝕔; constructor
  apply ctx𝕄.consℝ (fun X => .lam𝕔 {0 ↤ 2} X)
  apply ctxℝ.lam𝕔
  apply ctx𝕄.consℝ (fun X => .lets𝕔 (.load₁ x₁) {0 ↤ 3} X)
  apply ctxℝ.lets𝕔; constructor
  apply ctx𝕄.consℝ (fun X => .lets𝕔 (.binary₁ .mul x₂ x₃) {0 ↤ 4} X)
  apply ctxℝ.lets𝕔; constructor; constructor; constructor
  apply ctx𝕄.consℝ (fun X => .lets𝕔 (.store₁ x₁ x₄) {0 ↤ 5} X)
  apply ctxℝ.lets𝕔; constructor; constructor; constructor
  apply ctx𝕄.consℝ (fun X => .lets𝕔 (.load₁ x₁) {0 ↤ 6} X)
  apply ctxℝ.lets𝕔; constructor
  apply ctx𝕄.consℝ (fun X => .lets𝕔 (.binary₁ .mul x₂ x₆) {0 ↤ 7} X)
  apply ctxℝ.lets𝕔; constructor; constructor; constructor
  apply ctx𝕄.consℝ (fun X => .lets𝕔 (.store₁ x₁ x₇) {0 ↤ 8} X)
  apply ctxℝ.lets𝕔; constructor; constructor; constructor
  repeat constructor

example : (⟨ϵ, expr𝕩𝕩𝕩𝕩₃⟩ ⭢ ⟨ϵ, expr𝕩𝕩𝕩𝕩₄⟩) := by
  apply step_lvl.pure
    (fun X =>
      .lets𝕔 (.lit 1) { 0 ⇛
      .lets𝕔 (.alloc₁ x₀) { 1 ⇛
        .lam𝕔 { 2 ⇛
          .lets𝕔 (.load₁ x₁) { 3 ⇛
          .lets𝕔 (.binary₁ .mul x₂ x₃) { 4 ⇛
          .lets𝕔 (.store₁ x₁ x₄) { 5 ⇛
          .lets𝕔 (.load₁ x₁) { 6 ⇛
          .lets𝕔 (.binary₁ .mul x₂ x₆) { 7 ⇛
          X}}}}}}}})
  apply ctx𝕄.consℝ (fun X => .lets𝕔 (.lit 1) {0 ↤ 0} X)
  apply ctxℝ.lets𝕔; constructor
  apply ctx𝕄.consℝ (fun X => .lets𝕔 (.alloc₁ x₀) {0 ↤ 1} X)
  apply ctxℝ.lets𝕔; constructor
  apply ctx𝕄.consℝ (fun X => .lam𝕔 {0 ↤ 2} X)
  apply ctxℝ.lam𝕔
  apply ctx𝕄.consℝ (fun X => .lets𝕔 (.load₁ x₁) {0 ↤ 3} X)
  apply ctxℝ.lets𝕔; constructor
  apply ctx𝕄.consℝ (fun X => .lets𝕔 (.binary₁ .mul x₂ x₃) {0 ↤ 4} X)
  apply ctxℝ.lets𝕔; constructor; constructor; constructor
  apply ctx𝕄.consℝ (fun X => .lets𝕔 (.store₁ x₁ x₄) {0 ↤ 5} X)
  apply ctxℝ.lets𝕔; constructor; constructor; constructor
  apply ctx𝕄.consℝ (fun X => .lets𝕔 (.load₁ x₁) {0 ↤ 6} X)
  apply ctxℝ.lets𝕔; constructor
  apply ctx𝕄.consℝ (fun X => .lets𝕔 (.binary₁ .mul x₂ x₆) {0 ↤ 7} X)
  apply ctxℝ.lets𝕔; constructor; constructor; constructor
  repeat constructor

example : (⟨ϵ, expr𝕩𝕩𝕩𝕩₄⟩ ⭢ ⟨ϵ, expr𝕩𝕩𝕩𝕩₅⟩) := by
  apply step_lvl.pure
    (fun X =>
      .lets𝕔 (.lit 1) { 0 ⇛
      .lets𝕔 (.alloc₁ x₀) { 1 ⇛
        .lam𝕔 { 2 ⇛
          .lets𝕔 (.load₁ x₁) { 3 ⇛
          .lets𝕔 (.binary₁ .mul x₂ x₃) { 4 ⇛
          .lets𝕔 (.store₁ x₁ x₄) { 5 ⇛
          .lets𝕔 (.load₁ x₁) { 6 ⇛
          X}}}}}}})
  apply ctx𝕄.consℝ (fun X => .lets𝕔 (.lit 1) {0 ↤ 0} X)
  apply ctxℝ.lets𝕔; constructor
  apply ctx𝕄.consℝ (fun X => .lets𝕔 (.alloc₁ x₀) {0 ↤ 1} X)
  apply ctxℝ.lets𝕔; constructor
  apply ctx𝕄.consℝ (fun X => .lam𝕔 {0 ↤ 2} X)
  apply ctxℝ.lam𝕔
  apply ctx𝕄.consℝ (fun X => .lets𝕔 (.load₁ x₁) {0 ↤ 3} X)
  apply ctxℝ.lets𝕔; constructor
  apply ctx𝕄.consℝ (fun X => .lets𝕔 (.binary₁ .mul x₂ x₃) {0 ↤ 4} X)
  apply ctxℝ.lets𝕔; constructor; constructor; constructor
  apply ctx𝕄.consℝ (fun X => .lets𝕔 (.store₁ x₁ x₄) {0 ↤ 5} X)
  apply ctxℝ.lets𝕔; constructor; constructor; constructor
  apply ctx𝕄.consℝ (fun X => .lets𝕔 (.load₁ x₁) {0 ↤ 6} X)
  apply ctxℝ.lets𝕔; constructor
  repeat constructor

example : (⟨ϵ, expr𝕩𝕩𝕩𝕩₅⟩ ⭢ ⟨ϵ, expr𝕩𝕩𝕩𝕩₆⟩) := by
  apply step_lvl.pure
    (fun X =>
      .lets𝕔 (.lit 1) { 0 ⇛
      .lets𝕔 (.alloc₁ x₀) { 1 ⇛
        .lam𝕔 { 2 ⇛
          .lets𝕔 (.load₁ x₁) { 3 ⇛
          .lets𝕔 (.binary₁ .mul x₂ x₃) { 4 ⇛
          .lets𝕔 (.store₁ x₁ x₄) { 5 ⇛
          X}}}}}})
  apply ctx𝕄.consℝ (fun X => .lets𝕔 (.lit 1) {0 ↤ 0} X)
  apply ctxℝ.lets𝕔; constructor
  apply ctx𝕄.consℝ (fun X => .lets𝕔 (.alloc₁ x₀) {0 ↤ 1} X)
  apply ctxℝ.lets𝕔; constructor
  apply ctx𝕄.consℝ (fun X => .lam𝕔 {0 ↤ 2} X)
  apply ctxℝ.lam𝕔
  apply ctx𝕄.consℝ (fun X => .lets𝕔 (.load₁ x₁) {0 ↤ 3} X)
  apply ctxℝ.lets𝕔; constructor
  apply ctx𝕄.consℝ (fun X => .lets𝕔 (.binary₁ .mul x₂ x₃) {0 ↤ 4} X)
  apply ctxℝ.lets𝕔; constructor; constructor; constructor
  apply ctx𝕄.consℝ (fun X => .lets𝕔 (.store₁ x₁ x₄) {0 ↤ 5} X)
  apply ctxℝ.lets𝕔; constructor; constructor; constructor
  repeat constructor

example : (⟨ϵ, expr𝕩𝕩𝕩𝕩₆⟩ ⭢ ⟨ϵ, expr𝕩𝕩𝕩𝕩₇⟩) := by
  apply step_lvl.pure
    (fun X =>
      .lets𝕔 (.lit 1) { 0 ⇛
      .lets𝕔 (.alloc₁ x₀) { 1 ⇛
        .lam𝕔 { 2 ⇛
          .lets𝕔 (.load₁ x₁) { 3 ⇛
          .lets𝕔 (.binary₁ .mul x₂ x₃) { 4 ⇛
          X}}}}})
  apply ctx𝕄.consℝ (fun X => .lets𝕔 (.lit 1) {0 ↤ 0} X)
  apply ctxℝ.lets𝕔; constructor
  apply ctx𝕄.consℝ (fun X => .lets𝕔 (.alloc₁ x₀) {0 ↤ 1} X)
  apply ctxℝ.lets𝕔; constructor
  apply ctx𝕄.consℝ (fun X => .lam𝕔 {0 ↤ 2} X)
  apply ctxℝ.lam𝕔
  apply ctx𝕄.consℝ (fun X => .lets𝕔 (.load₁ x₁) {0 ↤ 3} X)
  apply ctxℝ.lets𝕔; constructor
  apply ctx𝕄.consℝ (fun X => .lets𝕔 (.binary₁ .mul x₂ x₃) {0 ↤ 4} X)
  apply ctxℝ.lets𝕔; constructor; constructor; constructor
  repeat constructor

example : (⟨ϵ, expr𝕩𝕩𝕩𝕩₇⟩ ⭢ ⟨ϵ, expr𝕩𝕩𝕩𝕩₈⟩) := by
  apply step_lvl.pure
    (fun X =>
      .lets𝕔 (.lit 1) { 0 ⇛
      .lets𝕔 (.alloc₁ x₀) { 1 ⇛
        .lam𝕔 { 2 ⇛
          .lets𝕔 (.load₁ x₁) { 3 ⇛
          X}}}})
  apply ctx𝕄.consℝ (fun X => .lets𝕔 (.lit 1) {0 ↤ 0} X)
  apply ctxℝ.lets𝕔; constructor
  apply ctx𝕄.consℝ (fun X => .lets𝕔 (.alloc₁ x₀) {0 ↤ 1} X)
  apply ctxℝ.lets𝕔; constructor
  apply ctx𝕄.consℝ (fun X => .lam𝕔 {0 ↤ 2} X)
  apply ctxℝ.lam𝕔
  apply ctx𝕄.consℝ (fun X => .lets𝕔 (.load₁ x₁) {0 ↤ 3} X)
  apply ctxℝ.lets𝕔; constructor
  repeat constructor

example : (⟨ϵ, expr𝕩𝕩𝕩𝕩₈⟩ ⭢ ⟨ϵ, expr𝕩𝕩𝕩𝕩₉⟩) := by
  apply step_lvl.pure
    (fun X =>
      .lets𝕔 (.lit 1) { 0 ⇛
      .lets𝕔 (.alloc₁ x₀) { 1 ⇛
        .lam𝕔 { 2 ⇛
          X}}})
  apply ctx𝕄.consℝ (fun X => .lets𝕔 (.lit 1) {0 ↤ 0} X)
  apply ctxℝ.lets𝕔; constructor
  apply ctx𝕄.consℝ (fun X => .lets𝕔 (.alloc₁ x₀) {0 ↤ 1} X)
  apply ctxℝ.lets𝕔; constructor
  apply ctx𝕄.consℝ (fun X => .lam𝕔 {0 ↤ 2} X)
  apply ctxℝ.lam𝕔
  repeat constructor

example : (⟨ϵ, expr𝕩𝕩𝕩𝕩₉⟩ ⭢ ⟨ϵ, expr𝕩𝕩𝕩𝕩𝕩₀⟩) := by
  apply step_lvl.pure
    (fun X =>
      .lets𝕔 (.lit 1) { 0 ⇛
      .lets𝕔 (.alloc₁ x₀) { 1 ⇛
      X}})
  apply ctx𝕄.consℝ (fun X => .lets𝕔 (.lit 1) {0 ↤ 0} X)
  apply ctxℝ.lets𝕔; constructor
  apply ctx𝕄.consℝ (fun X => .lets𝕔 (.alloc₁ x₀) {0 ↤ 1} X)
  apply ctxℝ.lets𝕔; constructor
  repeat constructor

example : (⟨ϵ, expr𝕩𝕩𝕩𝕩𝕩₀⟩ ⭢ ⟨ϵ, expr𝕩𝕩𝕩𝕩𝕩₁⟩) := by
  apply step_lvl.reflect
    (fun X =>
      .lets𝕔 (.lit 1) { 0 ⇛
      .lets𝕔 (.alloc₁ x₀) { 1 ⇛
      X}})
    id
  apply ctxℙ.consℚ
  apply ctxℚ.consℝ (fun X => .lets𝕔 (.lit 1) {0 ↤ 0} X)
  apply ctxℝ.lets𝕔; constructor
  apply ctxℚ.holeℝ (fun X => .lets𝕔 (.alloc₁ x₀) {0 ↤ 1} X)
  apply ctxℝ.lets𝕔; constructor
  repeat constructor

example : (⟨ϵ, expr𝕩𝕩𝕩𝕩𝕩₁⟩ ⭢ ⟨ϵ, expr𝕩𝕩𝕩𝕩𝕩₂⟩) := by
  apply step_lvl.pure
    (fun X =>
      .lets𝕔 (.lit 1) { 0 ⇛
      .lets𝕔 (.alloc₁ x₀) { 1 ⇛
      X}})
  apply ctx𝕄.consℝ (fun X => .lets𝕔 (.lit 1) {0 ↤ 0} X)
  apply ctxℝ.lets𝕔; constructor
  apply ctx𝕄.consℝ (fun X => .lets𝕔 (.alloc₁ x₀) {0 ↤ 1} X)
  apply ctxℝ.lets𝕔; constructor
  repeat constructor

example : (⟨ϵ, expr𝕩𝕩𝕩𝕩𝕩₂⟩ ⭢ ⟨ϵ, expr𝕩𝕩𝕩𝕩𝕩₃⟩) := by
  apply step_lvl.pure
    (fun X =>
      .lets𝕔 (.lit 1) { 0 ⇛
      X})
  apply ctx𝕄.consℝ (fun X => .lets𝕔 (.lit 1) {0 ↤ 0} X)
  apply ctxℝ.lets𝕔; constructor
  repeat constructor

example : (⟨ϵ, expr𝕩𝕩𝕩𝕩𝕩₃⟩ ⭢ ⟨ϵ, expr𝕩𝕩𝕩𝕩𝕩₄⟩) := by
  apply step_lvl.pure id
  repeat constructor

set_option maxRecDepth 1000 in
example : typing_reification ⦰ expr₀ (.rep (.arrow .nat .nat ⊥)) ⊤ :=
  by
  rw [← Effect.reify_union ⊤]; repeat constructor
  rw [← Effect.pure_union ⊤]; repeat constructor
  rw [Effect.reify_union ⊥]; repeat constructor
  rw [← Effect.union_reify (⊥ ∪ ⊤)]; repeat constructor
  rw [← Effect.reify_union ⊤]; repeat constructor
  rw [← Effect.union_pure ⊤, ← Effect.union_pure ⊤]; repeat constructor
  rw [← Effect.pure_union ⊥, ← Effect.pure_union ⊥]; repeat constructor

set_option maxRecDepth 2000 in
example : typing_reification ⦰ expr𝕩𝕩𝕩𝕩𝕩₄ (.rep (.arrow .nat .nat ⊥)) ⊥ :=
  by
  repeat
    first
    | constructor
    | rw [← Effect.union_pure ⊥]

end MutableStagePower
