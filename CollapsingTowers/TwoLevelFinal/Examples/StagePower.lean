import CollapsingTowers.TwoLevelFinal.Examples.Notation

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
-- ⇝*
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

example : (⟨ϵ, expr₀⟩ ⇝ ⟨ϵ, expr₁⟩) := by
  apply step_lvl.pure id
  repeat constructor

example : (⟨ϵ, expr₁⟩ ⇝ ⟨ϵ, expr₂⟩) := by
  apply step_lvl.pure id
  repeat constructor

example : (⟨ϵ, expr₂⟩ ⇝ ⟨ϵ, expr₃⟩) := by
  apply step_lvl.pure (fun X => .lam𝕔 ({0 ↤ 0} (.app₁ X _)))
  apply ctx𝕄.consℝ (fun X => .lam𝕔 ({0 ↤ 0} X))
  apply ctxℝ.lam𝕔
  apply ctx𝕄.cons𝔹 (fun X => .app₁ X _)
  repeat constructor

example : (⟨ϵ, expr₃⟩ ⇝ ⟨ϵ, expr₄⟩) := by
  apply step_lvl.pure (fun X => .lam𝕔 ({0 ↤ 0} (.app₁ X _)))
  apply ctx𝕄.consℝ (fun X => .lam𝕔 ({0 ↤ 0} X))
  apply ctxℝ.lam𝕔
  apply ctx𝕄.cons𝔹 (fun X => .app₁ X _)
  repeat constructor

example : (⟨ϵ, expr₄⟩ ⇝ ⟨ϵ, expr₅⟩) := by
  apply step_lvl.pure (fun X => .lam𝕔 ({0 ↤ 0} X))
  apply ctx𝕄.consℝ (fun X => .lam𝕔 ({0 ↤ 0} X))
  apply ctxℝ.lam𝕔
  repeat constructor

example : (⟨ϵ, expr₅⟩ ⇝ ⟨ϵ, expr₆⟩) := by
  let left : Expr :=
    .lam { 102 ⇛
          .lam { 103 ⇛
            .ifz₁ n (
              .lift (.lit 1)) (
              .binary₂ .mul (.code x₀) (.app₁ f (.binary₁ .sub n (.lit 1))))}}
  apply step_lvl.pure (fun X => .lam𝕔 ({0 ↤ 0} (.app₁ (.app₁ left X) _)))
  apply ctx𝕄.consℝ (fun X => .lam𝕔 ({0 ↤ 0} X))
  apply ctxℝ.lam𝕔
  apply ctx𝕄.cons𝔹 (fun X => .app₁ X _)
  repeat constructor

example : (⟨ϵ, expr₆⟩ ⇝ ⟨ϵ, expr₇⟩) := by
  apply step_lvl.pure (fun X => .lam𝕔 ({0 ↤ 0} (.app₁ X _)))
  apply ctx𝕄.consℝ (fun X => .lam𝕔 ({0 ↤ 0} X))
  apply ctxℝ.lam𝕔
  apply ctx𝕄.cons𝔹 (fun X => .app₁ X _)
  repeat constructor

example : (⟨ϵ, expr₇⟩ ⇝ ⟨ϵ, expr₈⟩) := by
  apply step_lvl.pure (fun X => .lam𝕔 ({0 ↤ 0} X))
  apply ctx𝕄.consℝ (fun X => .lam𝕔 ({0 ↤ 0} X))
  apply ctxℝ.lam𝕔
  repeat constructor

example : (⟨ϵ, expr₈⟩ ⇝ ⟨ϵ, expr₉⟩) := by
  apply step_lvl.pure (fun X => .lam𝕔 ({0 ↤ 0} X))
  apply ctx𝕄.consℝ (fun X => .lam𝕔 ({0 ↤ 0} X))
  apply ctxℝ.lam𝕔
  repeat constructor

example : (⟨ϵ, expr₉⟩ ⇝ ⟨ϵ, expr𝕩₀⟩) := by
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
  apply step_lvl.pure (fun X => .lam𝕔 ({0 ↤ 0} (.binary₂ .mul (.code x₀) (.app₁ left X))))
  apply ctx𝕄.consℝ (fun X => .lam𝕔 ({0 ↤ 0} X))
  apply ctxℝ.lam𝕔
  apply ctx𝕄.cons𝔹 (fun X => .binary₂ .mul (.code x₀) X)
  repeat constructor

example : (⟨ϵ, expr𝕩₀⟩ ⇝ ⟨ϵ, expr𝕩₁⟩) := by
  apply step_lvl.pure (fun X => .lam𝕔 ({0 ↤ 0} (.binary₂ .mul (.code x₀) X)))
  apply ctx𝕄.consℝ (fun X => .lam𝕔 ({0 ↤ 0} X))
  apply ctxℝ.lam𝕔
  apply ctx𝕄.cons𝔹 (fun X => .binary₂ .mul (.code x₀) X)
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

end StagePower
