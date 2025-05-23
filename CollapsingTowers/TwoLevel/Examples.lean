
import Mathlib.Data.Finset.Basic
import CollapsingTowers.TwoLevel.Syntax
import CollapsingTowers.TwoLevel.OpenClose
import CollapsingTowers.TwoLevel.Neutral
import CollapsingTowers.TwoLevel.Env
import CollapsingTowers.TwoLevel.SmallStep
import CollapsingTowers.TwoLevel.Typing

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
  .let𝕔 (.lam₁ (close₀ 0 (.lets (.plus₁ x₀ x₀) (close₀ 1 (.lets (.plus₁ x₀ x₁) (close₀ 2 x₂))))))
    (close₀ 3 (.code x₃))

def expr𝕩 : Expr :=
  .code
    (.lets (.lam₁ (close₀ 0 (.lets (.plus₁ x₀ x₀) (close₀ 1 (.lets (.plus₁ x₀ x₁) (close₀ 2 x₂)))))) (close₀ 3 x₃))

example : step expr₀ expr₁ := by
  apply step_lvl.step𝕄 _ _ _ ctx𝕄.hole
  repeat constructor

example : step expr₁ expr₂ := by
  apply step_lvl.step𝕄 _ _ _ (ctx𝕄.consℝ _ _ ctxℝ.lam𝕔 (ctx𝕄.cons𝔹 _ _ (ctx𝔹.plusr₂ _ _) ctx𝕄.hole))
  repeat constructor

example : step expr₂ expr₃ := by
  apply step_lvl.reflect _ _ _ (ctxℙℚ.consℝ _ _ ctxℝ.lam𝕔 ctxℙℚ.hole) (ctx𝔼.cons𝔹 _ _ (ctx𝔹.plusr₂ _ _) ctx𝔼.hole)
  repeat constructor

example : step expr₃ expr₄ := by
  apply step_lvl.step𝕄 _ _ _ (ctx𝕄.consℝ _ _ ctxℝ.lam𝕔 (ctx𝕄.consℝ _ _ (ctxℝ.let𝕔 _ _) ctx𝕄.hole))
  repeat constructor

example : step expr₄ expr₅ := by
  apply step_lvl.reflect _ _ _ (ctxℙℚ.consℝ _ _ ctxℝ.lam𝕔 (ctxℙℚ.consℝ _ _ (ctxℝ.let𝕔 _ _) ctxℙℚ.hole)) ctx𝔼.hole
  repeat constructor

example : step expr₅ expr₆ := by
  apply step_lvl.step𝕄 _ _ _ (ctx𝕄.consℝ _ _ ctxℝ.lam𝕔 (ctx𝕄.consℝ _ _ (ctxℝ.let𝕔 _ _) ctx𝕄.hole))
  repeat constructor

example : step expr₆ expr₇ := by
  apply step_lvl.step𝕄 _ _ _ (ctx𝕄.consℝ _ _ ctxℝ.lam𝕔 ctx𝕄.hole)
  repeat constructor

example : step expr₇ expr₈ := by
  simp; apply step_lvl.step𝕄 _ _ _ ctx𝕄.hole
  repeat constructor

example : step expr₈ expr₉ := by
  apply step_lvl.reflect _ _ _ ctxℙℚ.hole ctx𝔼.hole
  repeat constructor

example : step expr₉ expr𝕩 := by
  apply step_lvl.step𝕄 _ _ _ ctx𝕄.hole
  repeat constructor

example : typing [] expr₀ (.rep (.arrow .nat .nat)) :=
  by
  rw [expr₀, x₀]
  repeat constructor

example : typing [] expr₁ (.rep (.arrow .nat .nat)) :=
  by
  rw [expr₁, x₀]
  repeat constructor

example : typing [] expr₂ (.rep (.arrow .nat .nat)) :=
  by
  rw [expr₂, x₀]
  repeat constructor

example : typing [] expr₃ (.rep (.arrow .nat .nat)) :=
  by
  rw [expr₃, x₀, x₁]
  repeat constructor

example : typing [] expr₄ (.rep (.arrow .nat .nat)) :=
  by
  rw [expr₄, x₀, x₁]
  repeat constructor

example : typing [] expr₅ (.rep (.arrow .nat .nat)) :=
  by
  rw [expr₅, x₀, x₁, x₂]
  repeat constructor

example : typing [] expr₆ (.rep (.arrow .nat .nat)) :=
  by
  rw [expr₆, x₀, x₁, x₂]
  repeat constructor

example : typing [] expr₇ (.rep (.arrow .nat .nat)) :=
  by
  rw [expr₇, x₀, x₁, x₂]
  repeat constructor

example : typing [] expr₈ (.rep (.arrow .nat .nat)) :=
  by
  rw [expr₈, x₀, x₁, x₂]
  repeat constructor

example : typing [] expr₉ (.rep (.arrow .nat .nat)) :=
  by
  rw [expr₉, x₀, x₁, x₂]
  repeat constructor

example : typing [] expr𝕩 (.rep (.arrow .nat .nat)) :=
  by
  rw [expr𝕩, x₀, x₁, x₂]
  repeat constructor

end Example1

namespace Example2

/-- Example 2:
  app₂ (λ₂ (λ₁ x. x)) (lift (lit₁ 0))
→⋆
code {
  lets x1 = (λ₁ x. x) in
  lets x2 = app₁ x1 (lit₁ 0) in
  x2
}
-/

@[simp] def f : Expr := (.lift (.lam₁ (.bvar 0)))
@[simp] def i : Expr := (.lift (.lit₁ 0))

@[simp] def e1 : Expr := (.app₂ f i)
@[simp] def e2 : Expr := (.app₂ (.lam𝕔 (.code (.bvar 0))) i)
@[simp] def e3 : Expr := (.app₂ (.reflect (.lam₁ (.bvar 0))) i)
@[simp] def e4 : Expr := (.let𝕔 (.lam₁ (.bvar 0)) (.app₂ (.code (.bvar 0)) i))
@[simp] def e4' : Expr := (.let𝕔 (.lam₁ (.bvar 0)) (close₀ 0 (.app₂ (.code (.fvar 0)) i)))
@[simp] def e5 : Expr :=
  (.let𝕔 (.lam₁ (.bvar 0)) (close₀ 0 (.app₂ (.code (.fvar 0)) (.code (.lit₁ 0)))))
@[simp] def e6 : Expr :=
  (.let𝕔 (.lam₁ (.bvar 0)) (close₀ 0 (.reflect (.app₁ (.fvar 0) (.lit₁ 0)))))
@[simp] def e7 : Expr :=
  (.let𝕔 (.lam₁ (.bvar 0)) (close₀ 0 (.let𝕔 (.app₁ (.fvar 0) (.lit₁ 0)) (.code (.bvar 0)))))
@[simp] def e7' : Expr :=
  (.let𝕔 (.lam₁ (.bvar 0)) (close₀ 0 (.let𝕔 (.app₁ (.fvar 0) (.lit₁ 0)) (close₀ 1 (.code (.fvar 1))))))
@[simp] def e8 : Expr :=
  (.let𝕔 (.lam₁ (.bvar 0)) (close₀ 0 (.code (.lets (.app₁ (.fvar 0) (.lit₁ 0)) (.bvar 0)))))
@[simp] def e9 : Expr :=
  (.code (.lets (.lam₁ (.bvar 0)) (.lets (.app₁ (.bvar 0) (.lit₁ 0)) (.bvar 0))))

example : step e1 e2 := by
  simp; apply step_lvl.step𝕄 _ _ _ (ctx𝕄.cons𝔹 _ _ (ctx𝔹.appl₂ _ _) ctx𝕄.hole)
  repeat constructor

example : step e2 e3 := by
  simp; apply step_lvl.step𝕄 _ _ _ (ctx𝕄.cons𝔹 _ _ (ctx𝔹.appl₂ _ _) ctx𝕄.hole)
  repeat constructor

example : step e3 e4 := by
  apply step_lvl.reflect _ _ _ ctxℙℚ.hole
    (ctx𝔼.cons𝔹 (fun x => .app₂ x i) id (ctx𝔹.appl₂ _ (by aesop)) ctx𝔼.hole) (by aesop)

example : e4 = e4' := by simp

example : step e4' e5 := by
  apply step_lvl.step𝕄 (fun x => .let𝕔 (.lam₁ (.bvar 0)) (close₀ 0 (.app₂ (.code (.fvar 0)) x)))
  apply ctx𝕄.consℝ (fun x => .let𝕔 (.lam₁ (.bvar 0)) (close₀ 0 x))
  constructor; aesop; apply ctx𝕄.cons𝔹; apply ctx𝔹.appr₂; repeat constructor

example : step e5 e6 := by
  apply step_lvl.step𝕄 (fun x => .let𝕔 (.lam₁ (.bvar 0)) (close₀ 0 x))
  apply ctx𝕄.consℝ (fun x => .let𝕔 (.lam₁ (.bvar 0)) (close₀ 0 x))
  constructor; aesop; repeat constructor

example : step e6 e7 := by
  apply step_lvl.reflect (fun x => .let𝕔 (.lam₁ (.bvar 0)) (close₀ 0 x)) id
  apply ctxℙℚ.consℝ (fun x => .let𝕔 (.lam₁ (.bvar 0)) (close₀ 0 x))
  constructor; aesop; repeat constructor

example : e7 = e7' := by simp

example : step e7' e8 := by
  apply step_lvl.step𝕄 (fun x => .let𝕔 (.lam₁ (.bvar 0)) (close₀ 0 x))
  apply ctx𝕄.consℝ (fun x => .let𝕔 (.lam₁ (.bvar 0)) (close₀ 0 x))
  constructor; aesop; repeat constructor

example : step e8 e9 := by
  apply step_lvl.step𝕄 id; repeat constructor

end Example2

namespace Example3

/--
  lets f = {
    letc y = 42
    in lam₁ (code 1)
  } in
  f(0) +₂ f(0)
--/

-- stuck
@[simp] def e1 : Expr :=
  (.lets
    (.let𝕔 (.lit₁ 42)
      (.lam₁ /-int→rep(int)-/ (.code (.lit₁ 1))))
    (.plus₂ (.app₁ (.bvar 0) (.lit₁ 0)) (.app₁ (.bvar 0) (.lit₁ 1))))
end Example3
