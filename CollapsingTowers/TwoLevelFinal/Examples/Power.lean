import CollapsingTowers.TwoLevelFinal.Examples.Notation

-- naive power function xⁿ
namespace Power

--
--
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

example : typing_reification ⦰ expr₀ .nat ⊥ :=
  by
  repeat
    first
    | constructor
    | rw [← Effect.union_pure ⊥]
    | rw [Effect.union_pure ⊥]
