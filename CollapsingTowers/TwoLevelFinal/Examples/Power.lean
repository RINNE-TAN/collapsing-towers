import CollapsingTowers.TwoLevelFinal.Examples.Notation

-- naive power function xⁿ
namespace Power

-- let (power : ℕ → ℕ → ℕ) =
--   λ(x : ℕ).
--     fix₁ (
--       λ(f : ℕ → ℕ).
--       λ(n : ℕ).
--         ifz₁ n
--           then 1
--           else x * f(n - 1)
--     ) in
-- power(47)(2)
--
-- ⇝*
--
-- 2209

def power : Expr :=
  .fvar 0

def x : Expr :=
  .fvar 1

def f : Expr :=
  .fvar 2

def n : Expr :=
  .fvar 3

def expr₀ : Expr :=
  .lets (
    .lam { 1 ⇛
      .fix₁ (
        .lam { 2 ⇛
        .lam { 3 ⇛
          .ifz₁ n (
            .lit 1) (
            .binary₁ .mul x (.app₁ f (.binary₁ .sub n (.lit 1))))}})}) { 0 ⇛
  .app₁ (.app₁ power (.lit 47)) (.lit 2) }

def expr₁ : Expr :=
  .app₁ (
    .app₁ (
      .lam { 1 ⇛
        .fix₁ (
          .lam { 2 ⇛
          .lam { 3 ⇛
            .ifz₁ n (
              .lit 1) (
              .binary₁ .mul x (.app₁ f (.binary₁ .sub n (.lit 1))))}})}) (
      .lit 47)) (
    .lit 2)

def expr₂ : Expr :=
  .app₁ (
    .fix₁ (
      .lam { 2 ⇛
      .lam { 3 ⇛
        .ifz₁ n (
          .lit 1) (
          .binary₁ .mul (.lit 47) (.app₁ f (.binary₁ .sub n (.lit 1))))}})) (
    .lit 2)

def expr₃ : Expr :=
  .app₁ (
    .lam (
      .app₁ (
        .app₁ (
          .lam { 2 ⇛
          .lam { 3 ⇛
            .ifz₁ n (
              .lit 1) (
              .binary₁ .mul (.lit 47) (.app₁ f (.binary₁ .sub n (.lit 1))))}}) (
          .fix₁ (
            .lam { 2 ⇛
            .lam { 3 ⇛
              .ifz₁ n (
                .lit 1) (
                .binary₁ .mul (.lit 47) (.app₁ f (.binary₁ .sub n (.lit 1))))}}))) (
        .bvar 0))) (
    .lit 2)

def expr₄ : Expr :=
  .app₁ (
    .app₁ (
      .lam { 2 ⇛
      .lam { 3 ⇛
        .ifz₁ n (
          .lit 1) (
          .binary₁ .mul (.lit 47) (.app₁ f (.binary₁ .sub n (.lit 1))))}}) (
      .fix₁ (
        .lam { 2 ⇛
        .lam { 3 ⇛
          .ifz₁ n (
            .lit 1) (
            .binary₁ .mul (.lit 47) (.app₁ f (.binary₁ .sub n (.lit 1))))}}))) (
    .lit 2)

def expr₅ : Expr :=
  .app₁ (
    .app₁ (
      .lam { 2 ⇛
      .lam { 3 ⇛
        .ifz₁ n (
          .lit 1) (
          .binary₁ .mul (.lit 47) (.app₁ f (.binary₁ .sub n (.lit 1))))}}) (
      .lam (
        .app₁ (
          .app₁ (
            .lam { 2 ⇛
            .lam { 3 ⇛
              .ifz₁ n (
                .lit 1) (
                .binary₁ .mul (.lit 47) (.app₁ f (.binary₁ .sub n (.lit 1))))}}) (
            .fix₁ (
              .lam { 2 ⇛
              .lam { 3 ⇛
                .ifz₁ n (
                  .lit 1) (
                  .binary₁ .mul (.lit 47) (.app₁ f (.binary₁ .sub n (.lit 1))))}}))) (
          .bvar 0)))) (
    .lit 2)

def expr₆ : Expr :=
  .app₁ (
    .lam { 3 ⇛
      .ifz₁ n (
        .lit 1) (
        .binary₁ .mul (
          .lit 47) (
          .app₁ (
            .lam (
              .app₁ (
                .app₁ (
                  .lam { 2 ⇛
                  .lam { 3 ⇛
                    .ifz₁ n (
                      .lit 1) (
                      .binary₁ .mul (.lit 47) (.app₁ f (.binary₁ .sub n (.lit 1))))}}) (
                  .fix₁ (
                    .lam { 2 ⇛
                    .lam { 3 ⇛
                      .ifz₁ n (
                        .lit 1) (
                        .binary₁ .mul (.lit 47) (.app₁ f (.binary₁ .sub n (.lit 1))))}}))) (
                .bvar 0))) (
            .binary₁ .sub n (.lit 1))))}) (
    .lit 2)

def expr₇ : Expr :=
  .ifz₁ (.lit 2) (
    .lit 1) (
    .binary₁ .mul (
      .lit 47) (
      .app₁ (
        .lam (
          .app₁ (
            .app₁ (
              .lam { 2 ⇛
              .lam { 3 ⇛
                .ifz₁ n (
                  .lit 1) (
                  .binary₁ .mul (.lit 47) (.app₁ f (.binary₁ .sub n (.lit 1))))}}) (
              .fix₁ (
                .lam { 2 ⇛
                .lam { 3 ⇛
                  .ifz₁ n (
                    .lit 1) (
                    .binary₁ .mul (.lit 47) (.app₁ f (.binary₁ .sub n (.lit 1))))}}))) (
            .bvar 0))) (
        .binary₁ .sub (.lit 2) (.lit 1))))

def expr₈ : Expr :=
  .binary₁ .mul (
    .lit 47) (
    .app₁ (
      .lam (
        .app₁ (
          .app₁ (
            .lam { 2 ⇛
            .lam { 3 ⇛
              .ifz₁ n (
                .lit 1) (
                .binary₁ .mul (.lit 47) (.app₁ f (.binary₁ .sub n (.lit 1))))}}) (
            .fix₁ (
              .lam { 2 ⇛
              .lam { 3 ⇛
                .ifz₁ n (
                  .lit 1) (
                  .binary₁ .mul (.lit 47) (.app₁ f (.binary₁ .sub n (.lit 1))))}}))) (
          .bvar 0))) (
      .binary₁ .sub (.lit 2) (.lit 1)))

def expr₉ : Expr :=
  .binary₁ .mul (
    .lit 47) (
    .app₁ (
      .lam (
        .app₁ (
          .app₁ (
            .lam { 2 ⇛
            .lam { 3 ⇛
              .ifz₁ n (
                .lit 1) (
                .binary₁ .mul (.lit 47) (.app₁ f (.binary₁ .sub n (.lit 1))))}}) (
            .fix₁ (
              .lam { 2 ⇛
              .lam { 3 ⇛
                .ifz₁ n (
                  .lit 1) (
                  .binary₁ .mul (.lit 47) (.app₁ f (.binary₁ .sub n (.lit 1))))}}))) (
          .bvar 0))) (
      .lit 1))

def expr𝕩₀ : Expr :=
  .binary₁ .mul (
    .lit 47) (
      .app₁ (
        .app₁ (
          .lam { 2 ⇛
          .lam { 3 ⇛
            .ifz₁ n (
              .lit 1) (
              .binary₁ .mul (.lit 47) (.app₁ f (.binary₁ .sub n (.lit 1))))}}) (
          .fix₁ (
            .lam { 2 ⇛
            .lam { 3 ⇛
              .ifz₁ n (
                .lit 1) (
                .binary₁ .mul (.lit 47) (.app₁ f (.binary₁ .sub n (.lit 1))))}}))) (
        .lit 1))

def expr𝕩₁ : Expr :=
  .binary₁ .mul (
    .lit 47) (
      .app₁ (
        .app₁ (
          .lam { 2 ⇛
          .lam { 3 ⇛
            .ifz₁ n (
              .lit 1) (
              .binary₁ .mul (.lit 47) (.app₁ f (.binary₁ .sub n (.lit 1))))}}) (
          .lam (
            .app₁ (
              .app₁ (
                .lam { 2 ⇛
                .lam { 3 ⇛
                  .ifz₁ n (
                    .lit 1) (
                    .binary₁ .mul (.lit 47) (.app₁ f (.binary₁ .sub n (.lit 1))))}}) (
                .fix₁ (
                  .lam { 2 ⇛
                  .lam { 3 ⇛
                    .ifz₁ n (
                      .lit 1) (
                      .binary₁ .mul (.lit 47) (.app₁ f (.binary₁ .sub n (.lit 1))))}}))) (
              .bvar 0)))) (
        .lit 1))

def expr𝕩₂ : Expr :=
  .binary₁ .mul (
    .lit 47) (
      .app₁ (
        .lam { 3 ⇛
          .ifz₁ n (
            .lit 1) (
            .binary₁ .mul (
              .lit 47) (
              .app₁ (
                .lam (
                  .app₁ (
                    .app₁ (
                      .lam { 2 ⇛
                      .lam { 3 ⇛
                        .ifz₁ n (
                          .lit 1) (
                          .binary₁ .mul (.lit 47) (.app₁ f (.binary₁ .sub n (.lit 1))))}}) (
                      .fix₁ (
                        .lam { 2 ⇛
                        .lam { 3 ⇛
                          .ifz₁ n (
                            .lit 1) (
                            .binary₁ .mul (.lit 47) (.app₁ f (.binary₁ .sub n (.lit 1))))}}))) (
                    .bvar 0))) (
                .binary₁ .sub n (.lit 1))))}) (
        .lit 1))

def expr𝕩₃ : Expr :=
  .binary₁ .mul (
    .lit 47) (
    .ifz₁ (.lit 1) (
      .lit 1) (
      .binary₁ .mul (
        .lit 47) (
        .app₁ (
          .lam (
            .app₁ (
              .app₁ (
                .lam { 2 ⇛
                .lam { 3 ⇛
                  .ifz₁ n (
                    .lit 1) (
                    .binary₁ .mul (.lit 47) (.app₁ f (.binary₁ .sub n (.lit 1))))}}) (
                .fix₁ (
                  .lam { 2 ⇛
                  .lam { 3 ⇛
                    .ifz₁ n (
                      .lit 1) (
                      .binary₁ .mul (.lit 47) (.app₁ f (.binary₁ .sub n (.lit 1))))}}))) (
              .bvar 0))) (
          .binary₁ .sub (.lit 1) (.lit 1)))))

def expr𝕩₄ : Expr :=
  .binary₁ .mul (
    .lit 47) (
    .binary₁ .mul (
      .lit 47) (
      .app₁ (
        .lam (
          .app₁ (
            .app₁ (
              .lam { 2 ⇛
              .lam { 3 ⇛
                .ifz₁ n (
                  .lit 1) (
                  .binary₁ .mul (.lit 47) (.app₁ f (.binary₁ .sub n (.lit 1))))}}) (
              .fix₁ (
                .lam { 2 ⇛
                .lam { 3 ⇛
                  .ifz₁ n (
                    .lit 1) (
                    .binary₁ .mul (.lit 47) (.app₁ f (.binary₁ .sub n (.lit 1))))}}))) (
            .bvar 0))) (
        .binary₁ .sub (.lit 1) (.lit 1))))

def expr𝕩₅ : Expr :=
  .binary₁ .mul (
    .lit 47) (
    .binary₁ .mul (
      .lit 47) (
      .app₁ (
        .lam (
          .app₁ (
            .app₁ (
              .lam { 2 ⇛
              .lam { 3 ⇛
                .ifz₁ n (
                  .lit 1) (
                  .binary₁ .mul (.lit 47) (.app₁ f (.binary₁ .sub n (.lit 1))))}}) (
              .fix₁ (
                .lam { 2 ⇛
                .lam { 3 ⇛
                  .ifz₁ n (
                    .lit 1) (
                    .binary₁ .mul (.lit 47) (.app₁ f (.binary₁ .sub n (.lit 1))))}}))) (
            .bvar 0))) (
        .lit 0)))

def expr𝕩₆ : Expr :=
  .binary₁ .mul (
    .lit 47) (
    .binary₁ .mul (
      .lit 47) (
      .app₁ (
        .app₁ (
          .lam { 2 ⇛
          .lam { 3 ⇛
            .ifz₁ n (
              .lit 1) (
              .binary₁ .mul (.lit 47) (.app₁ f (.binary₁ .sub n (.lit 1))))}}) (
          .fix₁ (
            .lam { 2 ⇛
            .lam { 3 ⇛
              .ifz₁ n (
                .lit 1) (
                .binary₁ .mul (.lit 47) (.app₁ f (.binary₁ .sub n (.lit 1))))}}))) (
        .lit 0)))

def expr𝕩₇ : Expr :=
  .binary₁ .mul (
    .lit 47) (
    .binary₁ .mul (
      .lit 47) (
      .app₁ (
        .app₁ (
          .lam { 2 ⇛
          .lam { 3 ⇛
            .ifz₁ n (
              .lit 1) (
              .binary₁ .mul (.lit 47) (.app₁ f (.binary₁ .sub n (.lit 1))))}}) (
          .lam (
            .app₁ (
              .app₁ (
                .lam { 2 ⇛
                .lam { 3 ⇛
                  .ifz₁ n (
                    .lit 1) (
                    .binary₁ .mul (.lit 47) (.app₁ f (.binary₁ .sub n (.lit 1))))}}) (
                .fix₁ (
                  .lam { 2 ⇛
                  .lam { 3 ⇛
                    .ifz₁ n (
                      .lit 1) (
                      .binary₁ .mul (.lit 47) (.app₁ f (.binary₁ .sub n (.lit 1))))}}))) (
            .bvar 0)))) (
        .lit 0)))

def expr𝕩₈ : Expr :=
  .binary₁ .mul (
    .lit 47) (
    .binary₁ .mul (
      .lit 47) (
      .app₁ (
        .lam { 3 ⇛
          .ifz₁ n (
            .lit 1) (
            .binary₁ .mul (
              .lit 47) (
              .app₁ (
                .lam (
                  .app₁ (
                    .app₁ (
                      .lam { 2 ⇛
                      .lam { 3 ⇛
                        .ifz₁ n (
                          .lit 1) (
                          .binary₁ .mul (.lit 47) (.app₁ f (.binary₁ .sub n (.lit 1))))}}) (
                      .fix₁ (
                        .lam { 2 ⇛
                        .lam { 3 ⇛
                          .ifz₁ n (
                            .lit 1) (
                            .binary₁ .mul (.lit 47) (.app₁ f (.binary₁ .sub n (.lit 1))))}}))) (
                    .bvar 0))) (
                .binary₁ .sub n (.lit 1))))}) (
        .lit 0)))

def expr𝕩₉ : Expr :=
  .binary₁ .mul (
    .lit 47) (
    .binary₁ .mul (
      .lit 47) (
      .ifz₁ (.lit 0) (
        .lit 1) (
        .binary₁ .mul (
          .lit 47) (
          .app₁ (
            .lam (
              .app₁ (
                .app₁ (
                  .lam { 2 ⇛
                  .lam { 3 ⇛
                    .ifz₁ n (
                      .lit 1) (
                      .binary₁ .mul (.lit 47) (.app₁ f (.binary₁ .sub n (.lit 1))))}}) (
                  .fix₁ (
                    .lam { 2 ⇛
                    .lam { 3 ⇛
                      .ifz₁ n (
                        .lit 1) (
                        .binary₁ .mul (.lit 47) (.app₁ f (.binary₁ .sub n (.lit 1))))}}))) (
                .bvar 0))) (
            .binary₁ .sub (.lit 0) (.lit 1))))))

def expr𝕩𝕩₀ : Expr :=
  .binary₁ .mul (
    .lit 47) (
    .binary₁ .mul (
      .lit 47) (
      .lit 1))

def expr𝕩𝕩₁ : Expr :=
  .binary₁ .mul (
    .lit 47) (
    .lit 47)

def expr𝕩𝕩₂ : Expr :=
  .lit 2209

example : (⟨ϵ, expr₀⟩ ⇝ ⟨ϵ, expr₁⟩) := by
  apply step_lvl.pure id
  repeat constructor

example : (⟨ϵ, expr₁⟩ ⇝ ⟨ϵ, expr₂⟩) := by
  apply step_lvl.pure (fun X => .app₁ X _)
  apply ctx𝕄.cons𝔹 (fun X => .app₁ X _)
  repeat constructor

example : (⟨ϵ, expr₂⟩ ⇝ ⟨ϵ, expr₃⟩) := by
  apply step_lvl.pure (fun X => .app₁ X _)
  apply ctx𝕄.cons𝔹 (fun X => .app₁ X _)
  repeat constructor

example : (⟨ϵ, expr₃⟩ ⇝ ⟨ϵ, expr₄⟩) := by
  apply step_lvl.pure id
  repeat constructor

example : (⟨ϵ, expr₄⟩ ⇝ ⟨ϵ, expr₅⟩) := by
  let left : Expr :=
    .lam { 2 ⇛
    .lam { 3 ⇛
      .ifz₁ n (
        .lit 1) (
        .binary₁ .mul (.lit 47) (.app₁ f (.binary₁ .sub n (.lit 1))))}}
  apply step_lvl.pure (fun X => .app₁ (.app₁ left X) _)
  apply ctx𝕄.cons𝔹 (fun X => .app₁ X _)
  repeat constructor

example : (⟨ϵ, expr₅⟩ ⇝ ⟨ϵ, expr₆⟩) := by
  apply step_lvl.pure (fun X => .app₁ X _)
  apply ctx𝕄.cons𝔹 (fun X => .app₁ X _)
  repeat constructor

example : (⟨ϵ, expr₆⟩ ⇝ ⟨ϵ, expr₇⟩) := by
  apply step_lvl.pure id
  repeat constructor

example : (⟨ϵ, expr₇⟩ ⇝ ⟨ϵ, expr₈⟩) := by
  apply step_lvl.pure id
  repeat constructor

example : (⟨ϵ, expr₈⟩ ⇝ ⟨ϵ, expr₉⟩) := by
  let left : Expr :=
    .lam (
      .app₁ (
        .app₁ (
          .lam { 2 ⇛
          .lam { 3 ⇛
            .ifz₁ n (
              .lit 1) (
              .binary₁ .mul (.lit 47) (.app₁ f (.binary₁ .sub n (.lit 1))))}}) (
          .fix₁ (
            .lam { 2 ⇛
            .lam { 3 ⇛
              .ifz₁ n (
                .lit 1) (
                .binary₁ .mul (.lit 47) (.app₁ f (.binary₁ .sub n (.lit 1))))}}))) (
        .bvar 0))
  apply step_lvl.pure (fun X => .binary₁ .mul _ (.app₁ left X))
  repeat constructor

example : (⟨ϵ, expr₉⟩ ⇝ ⟨ϵ, expr𝕩₀⟩) := by
  apply step_lvl.pure (fun X => .binary₁ .mul _ X)
  repeat constructor

example : (⟨ϵ, expr𝕩₀⟩ ⇝ ⟨ϵ, expr𝕩₁⟩) := by
  let left : Expr :=
    .lam { 2 ⇛
    .lam { 3 ⇛
      .ifz₁ n (
        .lit 1) (
        .binary₁ .mul (.lit 47) (.app₁ f (.binary₁ .sub n (.lit 1))))}}
  apply step_lvl.pure (fun X => .binary₁ .mul _ (.app₁ (.app₁ left X) _))
  repeat constructor
  apply ctx𝕄.cons𝔹 (fun X => .app₁ X _)
  repeat constructor

example : (⟨ϵ, expr𝕩₁⟩ ⇝ ⟨ϵ, expr𝕩₂⟩) := by
  apply step_lvl.pure (fun X => .binary₁ .mul _ (.app₁ X _))
  repeat constructor
  apply ctx𝕄.cons𝔹 (fun X => .app₁ X _)
  repeat constructor

example : (⟨ϵ, expr𝕩₂⟩ ⇝ ⟨ϵ, expr𝕩₃⟩) := by
  apply step_lvl.pure (fun X => .binary₁ .mul _ X)
  repeat constructor

example : (⟨ϵ, expr𝕩₃⟩ ⇝ ⟨ϵ, expr𝕩₄⟩) := by
  apply step_lvl.pure (fun X => .binary₁ .mul _ X)
  repeat constructor

example : (⟨ϵ, expr𝕩₄⟩ ⇝ ⟨ϵ, expr𝕩₅⟩) := by
  let left : Expr :=
    .lam (
      .app₁ (
        .app₁ (
          .lam { 2 ⇛
          .lam { 3 ⇛
            .ifz₁ n (
              .lit 1) (
              .binary₁ .mul (.lit 47) (.app₁ f (.binary₁ .sub n (.lit 1))))}}) (
          .fix₁ (
            .lam { 2 ⇛
            .lam { 3 ⇛
              .ifz₁ n (
                .lit 1) (
                .binary₁ .mul (.lit 47) (.app₁ f (.binary₁ .sub n (.lit 1))))}}))) (
        .bvar 0))
  apply step_lvl.pure (fun X => .binary₁ .mul _ (.binary₁ .mul _ (.app₁ left X)))
  repeat constructor

example : (⟨ϵ, expr𝕩₅⟩ ⇝ ⟨ϵ, expr𝕩₆⟩) := by
  apply step_lvl.pure (fun X => .binary₁ .mul _ (.binary₁ .mul _ X))
  repeat constructor

example : (⟨ϵ, expr𝕩₆⟩ ⇝ ⟨ϵ, expr𝕩₇⟩) := by
  let left : Expr :=
    .lam { 2 ⇛
    .lam { 3 ⇛
      .ifz₁ n (
        .lit 1) (
        .binary₁ .mul (.lit 47) (.app₁ f (.binary₁ .sub n (.lit 1))))}}
  apply step_lvl.pure (fun X => .binary₁ .mul _ (.binary₁ .mul _ (.app₁ (.app₁ left X) _)))
  repeat constructor
  apply ctx𝕄.cons𝔹 (fun X => .app₁ X _)
  repeat constructor

example : (⟨ϵ, expr𝕩₇⟩ ⇝ ⟨ϵ, expr𝕩₈⟩) := by
  apply step_lvl.pure (fun X => .binary₁ .mul _ (.binary₁ .mul _ (.app₁ X _)))
  repeat constructor
  apply ctx𝕄.cons𝔹 (fun X => .app₁ X _)
  repeat constructor

example : (⟨ϵ, expr𝕩₈⟩ ⇝ ⟨ϵ, expr𝕩₉⟩) := by
  apply step_lvl.pure (fun X => .binary₁ .mul _ (.binary₁ .mul _ X))
  repeat constructor

example : (⟨ϵ, expr𝕩₉⟩ ⇝ ⟨ϵ, expr𝕩𝕩₀⟩) := by
  apply step_lvl.pure (fun X => .binary₁ .mul _ (.binary₁ .mul _ X))
  repeat constructor

example : (⟨ϵ, expr𝕩𝕩₀⟩ ⇝ ⟨ϵ, expr𝕩𝕩₁⟩) := by
  apply step_lvl.pure (fun X => .binary₁ .mul _ X)
  repeat constructor

example : (⟨ϵ, expr𝕩𝕩₁⟩ ⇝ ⟨ϵ, expr𝕩𝕩₂⟩) := by
  apply step_lvl.pure id
  repeat constructor

example : typing_reification ⦰ expr₀ .nat ⊥ :=
  by
  repeat
    first
    | constructor
    | rw [← Effect.union_pure ⊥]
    | rw [Effect.union_pure ⊥]

example : typing_reification ⦰ expr𝕩𝕩₂ .nat ⊥ :=
  by
  repeat
    first
    | constructor
    | rw [← Effect.union_pure ⊥]
    | rw [Effect.union_pure ⊥]

end Power
