
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
--           else x * f(n - 1)
--     ) in
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
          .lit 47) (
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

example : step ([], expr₀) ([], expr₁) := by
  apply step_lvl.step𝕄 id
  repeat constructor

example : step ([], expr₁) ([], expr₂) := by
  apply step_lvl.step𝕄 (fun X => .app₁ X _)
  apply ctx𝕄.cons𝔹 (fun X => .app₁ X _)
  repeat constructor

example : step ([], expr₂) ([], expr₃) := by
  apply step_lvl.step𝕄 (fun X => .app₁ X _)
  apply ctx𝕄.cons𝔹 (fun X => .app₁ X _)
  repeat constructor

example : step ([], expr₃) ([], expr₄) := by
  apply step_lvl.step𝕄 id
  repeat constructor

example : step ([], expr₄) ([], expr₅) := by
  apply step_lvl.step𝕄 id
  repeat constructor

example : step ([], expr₅) ([], expr₆) := by
  apply step_lvl.step𝕄 (fun X => .binary₁ .mul _ (.app₁ X _))
  apply ctx𝕄.cons𝔹 (fun X => .binary₁ .mul _ X)
  repeat constructor
  apply ctx𝕄.cons𝔹 (fun X => .app₁ X _)
  repeat constructor

example : step ([], expr₆) ([], expr₇) := by
  let left : Expr :=
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
          .binary₁ .sub n (.lit 1))))))
  apply step_lvl.step𝕄 (fun X => .binary₁ .mul _ (.app₁ left X))
  repeat constructor

example : step ([], expr₇) ([], expr₈) := by
  apply step_lvl.step𝕄 (fun X => .binary₁ .mul _ X)
  repeat constructor

example : step ([], expr₈) ([], expr₉) := by
  apply step_lvl.step𝕄 (fun X => .binary₁ .mul _ X)
  repeat constructor

example : step ([], expr₉) ([], expr𝕩₀) := by
  apply step_lvl.step𝕄 (fun X => .binary₁ .mul _ (.binary₁ .mul _ (.app₁ X _)))
  repeat constructor
  apply ctx𝕄.cons𝔹 (fun X => .app₁ X _)
  repeat constructor

example : step ([], expr𝕩₀) ([], expr𝕩₁) := by
  let left : Expr :=
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
          .binary₁ .sub n (.lit 1))))))
  apply step_lvl.step𝕄 (fun X => .binary₁ .mul _ (.binary₁ .mul _ (.app₁ left X)))
  repeat constructor

example : step ([], expr𝕩₁) ([], expr𝕩₂) := by
  apply step_lvl.step𝕄 (fun X => .binary₁ .mul _ (.binary₁ .mul _ X))
  repeat constructor

example : step ([], expr𝕩₂) ([], expr𝕩₃) := by
  apply step_lvl.step𝕄 (fun X => .binary₁ .mul _ (.binary₁ .mul _ X))
  repeat constructor

example : step ([], expr𝕩₃) ([], expr𝕩₄) := by
  apply step_lvl.step𝕄 (fun X => .binary₁ .mul _ X)
  repeat constructor

example : step ([], expr𝕩₄) ([], expr𝕩₅) := by
  apply step_lvl.step𝕄 id
  repeat constructor

example : typing_reification [] [] expr₀ .nat ∅ :=
  by
  repeat
    first
    | constructor
    | rw [← union_pure_left ∅]

example : typing_reification [] [] expr₁ .nat ∅ :=
  by
  repeat
    first
    | constructor
    | rw [← union_pure_left ∅]

example : typing_reification [] [] expr₂ .nat ∅ :=
  by
  repeat
    first
    | constructor
    | rw [← union_pure_left ∅]

example : typing_reification [] [] expr₃ .nat ∅ :=
  by
  repeat
    first
    | constructor
    | rw [← union_pure_left ∅]

example : typing_reification [] [] expr₄ .nat ∅ :=
  by
  repeat
    first
    | constructor
    | rw [← union_pure_left ∅]

example : typing_reification [] [] expr₅ .nat ∅ :=
  by
  repeat
    first
    | constructor
    | rw [← union_pure_left ∅]

example : typing_reification [] [] expr₆ .nat ∅ :=
  by
  repeat
    first
    | constructor
    | rw [← union_pure_left ∅]

example : typing_reification [] [] expr₇ .nat ∅ :=
  by
  repeat
    first
    | constructor
    | rw [← union_pure_left ∅]

example : typing_reification [] [] expr₈ .nat ∅ :=
  by
  repeat
    first
    | constructor
    | rw [← union_pure_left ∅]

example : typing_reification [] [] expr₉ .nat ∅ :=
  by
  repeat
    first
    | constructor
    | rw [← union_pure_left ∅]


example : typing_reification [] [] expr𝕩₀ .nat ∅ :=
  by
  repeat
    first
    | constructor
    | rw [← union_pure_left ∅]

example : typing_reification [] [] expr𝕩₁ .nat ∅ :=
  by
  repeat
    first
    | constructor
    | rw [← union_pure_left ∅]

example : typing_reification [] [] expr𝕩₂ .nat ∅ :=
  by
  repeat
    first
    | constructor
    | rw [← union_pure_left ∅]

example : typing_reification [] [] expr𝕩₃ .nat ∅ :=
  by
  repeat
    first
    | constructor
    | rw [← union_pure_left ∅]

example : typing_reification [] [] expr𝕩₄ .nat ∅ :=
  by
  repeat
    first
    | constructor
    | rw [← union_pure_left ∅]

example : typing_reification [] [] expr𝕩₅ .nat ∅ :=
  by
  repeat
    first
    | constructor
    | rw [← union_pure_left ∅]
end Power

namespace PowerMutable
-- mutable power function xⁿ
-- let res = alloc₁ 1 in
-- let (power : ℕ → ℕ → Unit) =
--   λ(x : ℕ).
--     fix₁ (
--       λ(f : ℕ → Unit).
--       λ(n : ℕ).
--         ifz₁ n
--           then unit
--           else
--            let _ = store₁ res (x * (load₁ res)) in
--            f(n - 1)
--     ) in
-- power 47 2
def ref : Expr :=
  .fvar 0

def power : Expr :=
  .fvar 1

def x : Expr :=
  .fvar 2

def f : Expr :=
  .fvar 3

def n : Expr :=
  .fvar 4

def expr₀ : Expr :=
  .lets (.alloc₁ (.lit 1)) (close₀ 0 (
  .lets (
    .lam (close₀ 2 (
      .fix₁ (
        .lam (close₀ 3 (
        .lam (close₀ 4 (
          .ifz₁ n (
            .unit) (
            .lets (.store₁ ref (.binary₁ .mul x (.load₁ ref))) (
            .app₁ f (.binary₁ .sub n (.lit 1)))))))))))) (close₀ 1 (
  .app₁ (.app₁ power (.lit 47)) (.lit 2)))))

def expr₁ : Expr :=
  .lets (.loc 0) (close₀ 0 (
  .lets (
    .lam (close₀ 2 (
      .fix₁ (
        .lam (close₀ 3 (
        .lam (close₀ 4 (
          .ifz₁ n (
            .unit) (
            .lets (.store₁ ref (.binary₁ .mul x (.load₁ ref))) (
            .app₁ f (.binary₁ .sub n (.lit 1)))))))))))) (close₀ 1 (
  .app₁ (.app₁ power (.lit 47)) (.lit 2)))))

def expr₂ : Expr :=
  .lets (
    .lam (close₀ 2 (
      .fix₁ (
        .lam (close₀ 3 (
        .lam (close₀ 4 (
          .ifz₁ n (
            .unit) (
            .lets (.store₁ (.loc 0) (.binary₁ .mul x (.load₁ (.loc 0)))) (
            .app₁ f (.binary₁ .sub n (.lit 1)))))))))))) (close₀ 1 (
  .app₁ (.app₁ power (.lit 47)) (.lit 2)))

def expr₃ : Expr :=
  .app₁ (
    .app₁ (
      .lam (close₀ 2 (
        .fix₁ (
          .lam (close₀ 3 (
          .lam (close₀ 4 (
            .ifz₁ n (
              .unit) (
              .lets (.store₁ (.loc 0) (.binary₁ .mul x (.load₁ (.loc 0)))) (
              .app₁ f (.binary₁ .sub n (.lit 1)))))))))))) (
      .lit 47)) (
    .lit 2)

def expr₄ : Expr :=
  .app₁ (
    .fix₁ (
      .lam (close₀ 3 (
      .lam (close₀ 4 (
        .ifz₁ n (
          .unit) (
          .lets (.store₁ (.loc 0) (.binary₁ .mul (.lit 47) (.load₁ (.loc 0)))) (
          .app₁ f (.binary₁ .sub n (.lit 1)))))))))) (
    .lit 2)

def expr₅ : Expr :=
  .app₁ (
    .lam (close₀ 4 (
      .ifz₁ n (
        .unit) (
        .lets (.store₁ (.loc 0) (.binary₁ .mul (.lit 47) (.load₁ (.loc 0)))) (
        .app₁ (
          .fix₁ (
            .lam (close₀ 3 (
            .lam (close₀ 4 (
              .ifz₁ n (
                .unit) (
                .lets (.store₁ (.loc 0) (.binary₁ .mul (.lit 47) (.load₁ (.loc 0)))) (
                .app₁ f (.binary₁ .sub n (.lit 1)))))))))) (
          .binary₁ .sub n (.lit 1))))))) (
    .lit 2)

def expr₆ : Expr :=
  .ifz₁ (.lit 2) (
    .unit) (
    .lets (.store₁ (.loc 0) (.binary₁ .mul (.lit 47) (.load₁ (.loc 0)))) (
    .app₁ (
      .fix₁ (
        .lam (close₀ 3 (
        .lam (close₀ 4 (
          .ifz₁ n (
            .unit) (
            .lets (.store₁ (.loc 0) (.binary₁ .mul (.lit 47) (.load₁ (.loc 0)))) (
            .app₁ f (.binary₁ .sub n (.lit 1)))))))))) (
      .binary₁ .sub (.lit 2) (.lit 1))))

def expr₇ : Expr :=
  .lets (.store₁ (.loc 0) (.binary₁ .mul (.lit 47) (.load₁ (.loc 0)))) (
  .app₁ (
    .fix₁ (
      .lam (close₀ 3 (
      .lam (close₀ 4 (
        .ifz₁ n (
          .unit) (
          .lets (.store₁ (.loc 0) (.binary₁ .mul (.lit 47) (.load₁ (.loc 0)))) (
          .app₁ f (.binary₁ .sub n (.lit 1)))))))))) (
    .binary₁ .sub (.lit 2) (.lit 1)))

example : step ([], expr₀) ([.lit 1], expr₁) := by
  apply step_lvl.store𝕄 (fun X => .lets X _)
  apply ctx𝕄.cons𝔹 (fun X => .lets X _)
  repeat constructor

example : step ([.lit 1], expr₁) ([.lit 1], expr₂) := by
  apply step_lvl.step𝕄 id
  repeat constructor

example : step ([.lit 1], expr₂) ([.lit 1], expr₃) := by
  apply step_lvl.step𝕄 id
  repeat constructor

example : step ([.lit 1], expr₃) ([.lit 1], expr₄) := by
  apply step_lvl.step𝕄 (fun X => .app₁ X _)
  apply ctx𝕄.cons𝔹 (fun X => .app₁ X _)
  repeat constructor

example : step ([.lit 1], expr₄) ([.lit 1], expr₅) := by
  apply step_lvl.step𝕄 (fun X => .app₁ X _)
  apply ctx𝕄.cons𝔹 (fun X => .app₁ X _)
  repeat constructor

example : step ([.lit 1], expr₅) ([.lit 1], expr₆) := by
  apply step_lvl.step𝕄 id
  repeat constructor

example : step ([.lit 1], expr₆) ([.lit 1], expr₇) := by
  apply step_lvl.step𝕄 id
  repeat constructor

set_option maxRecDepth 1000 in
example : typing_reification [] [] expr₀ .unit ∅ :=
  by
  repeat
    first
    | constructor
    | rw [← union_pure_left ∅]

set_option maxRecDepth 1000 in
example : typing_reification [] [.nat] expr₁ .unit ∅ :=
  by
  repeat
    first
    | constructor
    | rw [← union_pure_left ∅]

set_option maxRecDepth 1000 in
example : typing_reification [] [.nat] expr₂ .unit ∅ :=
  by
  repeat
    first
    | constructor
    | rw [← union_pure_left ∅]

set_option maxRecDepth 1000 in
example : typing_reification [] [.nat] expr₃ .unit ∅ :=
  by
  repeat
    first
    | constructor
    | rw [← union_pure_left ∅]

set_option maxRecDepth 1000 in
example : typing_reification [] [.nat] expr₄ .unit ∅ :=
  by
  repeat
    first
    | constructor
    | rw [← union_pure_left ∅]

set_option maxRecDepth 1000 in
example : typing_reification [] [.nat] expr₅ .unit ∅ :=
  by
  repeat
    first
    | constructor
    | rw [← union_pure_left ∅]

set_option maxRecDepth 1000 in
example : typing_reification [] [.nat] expr₆ .unit ∅ :=
  by
  repeat
    first
    | constructor
    | rw [← union_pure_left ∅]

set_option maxRecDepth 1000 in
example : typing_reification [] [.nat] expr₇ .unit ∅ :=
  by
  repeat
    first
    | constructor
    | rw [← union_pure_left ∅]
end PowerMutable
