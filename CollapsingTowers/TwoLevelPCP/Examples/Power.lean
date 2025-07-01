
import CollapsingTowers.TwoLevelPCP.Typing
namespace Power
-- naive power function xⁿ
-- let (power : ℕ → ℕ → ℕ) =
--   λ(x : ℕ).
--     fix₁ (
--       λ(f : ℕ → ℕ).
--       λ(n : ℕ).
--         ifz₁ n
--           then 1
--           else x * f(n-1)
--     )
-- power 47 2
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
    .lam (close₀ 1 (
      .fix₁ (
        .lam (close₀ 2 (
        .lam (close₀ 3 (
          .ifz₁ n (
            .lit 1) (
            .binary₁ .mul x (.app₁ f (.binary₁ .sub n (.lit 1)))))))))))) (close₀ 0 (
  .app₁ (.app₁ power (.lit 47)) (.lit 2)))

def expr₁ : Expr :=
  .app₁ (
    .app₁ (
      .lam (close₀ 1 (
        .fix₁ (
          .lam (close₀ 2 (
          .lam (close₀ 3 (
            .ifz₁ n (
              .lit 1) (
              .binary₁ .mul x (.app₁ f (.binary₁ .sub n (.lit 1)))))))))))) (
    .lit 47)) (
  .lit 2)

def expr₂ : Expr :=
  .app₁ (
    .fix₁ (
      .lam (close₀ 2 (
      .lam (close₀ 3 (
        .ifz₁ n (
          .lit 1) (
          .binary₁ .mul (.lit 47) (.app₁ f (.binary₁ .sub n (.lit 1)))))))))) (
  .lit 2)

def expr₃ : Expr :=
  .app₁ (
    .lam (close₀ 3 (
      .ifz₁ n (
        .lit 1) (
        .binary₁ .mul (
          .lit 2) (
          .app₁ (
            .fix₁ (
              .lam (close₀ 2 (
              .lam (close₀ 3 (
                .ifz₁ n (
                  .lit 1) (
                  .binary₁ .mul (.lit 47) (.app₁ f (.binary₁ .sub n (.lit 1)))))))))) (
            .binary₁ .sub n (.lit 1))))))) (
  .lit 2)

def expr₄ : Expr :=
  .ifz₁ (.lit 2) (
    .lit 1) (
    .binary₁ .mul (
      .lit 47) (
      .app₁ (
        .fix₁ (
          .lam (close₀ 2 (
          .lam (close₀ 3 (
            .ifz₁ n (
              .lit 1) (
              .binary₁ .mul (.lit 47) (.app₁ f (.binary₁ .sub n (.lit 1)))))))))) (
        .binary₁ .sub (.lit 2) (.lit 1))))

def expr₅ : Expr :=
  .binary₁ .mul (
    .lit 47) (
    .app₁ (
      .fix₁ (
        .lam (close₀ 2 (
        .lam (close₀ 3 (
          .ifz₁ n (
            .lit 1) (
            .binary₁ .mul (.lit 47) (.app₁ f (.binary₁ .sub n (.lit 1)))))))))) (
      .binary₁ .sub (.lit 2) (.lit 1)))

def expr₆ : Expr :=
  .binary₁ .mul (
    .lit 47) (
    .app₁ (
      .lam (close₀ 3 (
        .ifz₁ n (
          .lit 1) (
          .binary₁ .mul (
            .lit 47) (
            .app₁ (.fix₁ (
              .lam (close₀ 2 (
              .lam (close₀ 3 (
                .ifz₁ n (
                  .lit 1) (
                  .binary₁ .mul (.lit 47) (.app₁ f (.binary₁ .sub n (.lit 1)))))))))) (
            .binary₁ .sub n (.lit 1))))))) (
      .binary₁ .sub (.lit 2) (.lit 1)))

def expr₇ : Expr :=
  .binary₁ .mul (
    .lit 47) (
    .app₁ (
      .lam (close₀ 3 (
        .ifz₁ n (
          .lit 1) (
          .binary₁ .mul (
            .lit 47) (
            .app₁ (.fix₁ (
              .lam (close₀ 2 (
              .lam (close₀ 3 (
                .ifz₁ n (
                  .lit 1) (
                  .binary₁ .mul (.lit 47) (.app₁ f (.binary₁ .sub n (.lit 1)))))))))) (
              .binary₁ .sub n (.lit 1))))))) (
      .lit 1))

def expr₈ : Expr :=
  .binary₁ .mul (
    .lit 47) (
    .ifz₁ (.lit 1) (
      .lit 1) (
      .binary₁ .mul (
        .lit 47) (
        .app₁ (.fix₁ (
          .lam (close₀ 2 (
          .lam (close₀ 3 (
            .ifz₁ n (
              .lit 1) (
              .binary₁ .mul (.lit 47) (.app₁ f (.binary₁ .sub n (.lit 1)))))))))) (
          .binary₁ .sub (.lit 1) (.lit 1)))))

def expr₉ : Expr :=
  .binary₁ .mul (
    .lit 47) (
    .binary₁ .mul (
      .lit 47) (
      .app₁ (.fix₁ (
        .lam (close₀ 2 (
        .lam (close₀ 3 (
          .ifz₁ n (
            .lit 1) (
            .binary₁ .mul (.lit 47) (.app₁ f (.binary₁ .sub n (.lit 1)))))))))) (
        .binary₁ .sub (.lit 1) (.lit 1))))

def expr𝕩₀ : Expr :=
  .binary₁ .mul (
    .lit 47) (
    .binary₁ .mul (
      .lit 47) (
      .app₁ (
        .lam (close₀ 3 (
          .ifz₁ n (
            .lit 1) (
            .binary₁ .mul (
              .lit 47) (
              .app₁ (
                .fix₁ (
                  .lam (close₀ 2 (
                  .lam (close₀ 3 (
                    .ifz₁ n (
                      .lit 1) (
                      .binary₁ .mul (.lit 47) (.app₁ f (.binary₁ .sub n (.lit 1)))))))))) (
                .binary₁ .sub n (.lit 1))))))) (
        .binary₁ .sub (.lit 1) (.lit 1))))

def expr𝕩₁ : Expr :=
  .binary₁ .mul (
    .lit 47) (
    .binary₁ .mul (
      .lit 47) (
      .app₁ (
        .lam (close₀ 3 (
          .ifz₁ n (
            .lit 1) (
            .binary₁ .mul (
              .lit 47) (
              .app₁ (
                .fix₁ (
                  .lam (close₀ 2 (
                  .lam (close₀ 3 (
                    .ifz₁ n (
                      .lit 1) (
                      .binary₁ .mul (.lit 47) (.app₁ f (.binary₁ .sub n (.lit 1)))))))))) (
                .binary₁ .sub n (.lit 1))))))) (
        .lit 0)))

def expr𝕩₂ : Expr :=
  .binary₁ .mul (
    .lit 47) (
    .binary₁ .mul (
      .lit 47) (
      .ifz₁ (.lit 0) (
        .lit 1) (
        .binary₁ .mul (
          .lit 47) (
          .app₁ (
            .fix₁ (
              .lam (close₀ 2 (
              .lam (close₀ 3 (
                .ifz₁ n (
                  .lit 1) (
                  .binary₁ .mul (.lit 47) (.app₁ f (.binary₁ .sub n (.lit 1)))))))))) (
            .binary₁ .sub (.lit 0) (.lit 1))))))

def expr𝕩₃ : Expr :=
  .binary₁ .mul (
    .lit 47) (
    .binary₁ .mul (
      .lit 47) (
      .lit 1))

def expr𝕩₄ : Expr :=
  .binary₁ .mul (
    .lit 47) (
    .lit 47)

def expr𝕩₅ : Expr := .lit 2209

example : typing_reification [] [] expr₀ .nat ∅ :=
  by
  rw [expr₀, power, x, f, n]
  repeat
    first
    | constructor
    | rw [← union_pure_left ∅]

example : typing_reification [] [] expr₁ .nat ∅ :=
  by
  rw [expr₁, x, f, n]
  repeat
    first
    | constructor
    | rw [← union_pure_left ∅]

example : typing_reification [] [] expr₂ .nat ∅ :=
  by
  rw [expr₂, f, n]
  repeat
    first
    | constructor
    | rw [← union_pure_left ∅]

example : typing_reification [] [] expr₃ .nat ∅ :=
  by
  rw [expr₃, f, n]
  repeat
    first
    | constructor
    | rw [← union_pure_left ∅]

example : typing_reification [] [] expr₄ .nat ∅ :=
  by
  rw [expr₄, f, n]
  repeat
    first
    | constructor
    | rw [← union_pure_left ∅]

example : typing_reification [] [] expr₅ .nat ∅ :=
  by
  rw [expr₅, f, n]
  repeat
    first
    | constructor
    | rw [← union_pure_left ∅]

example : typing_reification [] [] expr₆ .nat ∅ :=
  by
  rw [expr₆, f, n]
  repeat
    first
    | constructor
    | rw [← union_pure_left ∅]

example : typing_reification [] [] expr₇ .nat ∅ :=
  by
  rw [expr₇, f, n]
  repeat
    first
    | constructor
    | rw [← union_pure_left ∅]

example : typing_reification [] [] expr₈ .nat ∅ :=
  by
  rw [expr₈, f, n]
  repeat
    first
    | constructor
    | rw [← union_pure_left ∅]

example : typing_reification [] [] expr₉ .nat ∅ :=
  by
  rw [expr₉, f, n]
  repeat
    first
    | constructor
    | rw [← union_pure_left ∅]


example : typing_reification [] [] expr𝕩₀ .nat ∅ :=
  by
  rw [expr𝕩₀, f, n]
  repeat
    first
    | constructor
    | rw [← union_pure_left ∅]

example : typing_reification [] [] expr𝕩₁ .nat ∅ :=
  by
  rw [expr𝕩₁, f, n]
  repeat
    first
    | constructor
    | rw [← union_pure_left ∅]

example : typing_reification [] [] expr𝕩₂ .nat ∅ :=
  by
  rw [expr𝕩₂, f, n]
  repeat
    first
    | constructor
    | rw [← union_pure_left ∅]

example : typing_reification [] [] expr𝕩₃ .nat ∅ :=
  by
  rw [expr𝕩₃]
  repeat
    first
    | constructor
    | rw [← union_pure_left ∅]

example : typing_reification [] [] expr𝕩₄ .nat ∅ :=
  by
  rw [expr𝕩₄]
  repeat
    first
    | constructor
    | rw [← union_pure_left ∅]

example : typing_reification [] [] expr𝕩₅ .nat ∅ :=
  by
  rw [expr𝕩₅]
  repeat
    first
    | constructor
    | rw [← union_pure_left ∅]
end Power
