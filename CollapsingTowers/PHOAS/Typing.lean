
import CollapsingTowers.PHOAS.Basic
import CollapsingTowers.PHOAS.SmallStep
inductive typing : Expr -> Ty -> Prop where
  | var : ∀ τ, typing (var τ) (@τ Ty)
  | lam : ∀ e τ𝕒 τ𝕓, typing (apply𝕍 e τ𝕒) τ𝕓 -> typing (lam e) (.arrow (@τ𝕒 Ty) τ𝕓)
  | app : ∀ f arg τ𝕒 τ𝕓, typing f τ𝕓 -> typing arg τ𝕒 -> typing (app f arg) τ𝕓
  | unit : typing unit .unit

theorem preservation : ∀ e₀ e₁ τ, step e₀ e₁ -> typing e₀ τ -> typing e₁ τ :=
  by
  intros e₀ e₁ τ Hstep
  induction Hstep with
  | appβ M v e HM Hvalue =>
    induction HM with
    | hole =>
      simp
      generalize HEqf₀ : (fun {𝕍} => lam e) = f₀
      generalize HEqarg₀ : (fun {𝕍} => v) = arg₀
      generalize HEqe₀ : (fun {𝕍} => app f₀ arg₀) = e₀
      intro Htye₀
      cases Htye₀ with
      | app f arg τ𝕒 τ𝕓 Htyf Htyarg =>
        have HEqe₀ := congrFun HEqe₀ Empty
        rw [app] at HEqe₀
        rw [app] at HEqe₀
        simp at HEqe₀
        admit
      | var =>
        have HEqe₀ := congrFun HEqe₀ Empty
        rw [app] at HEqe₀
        rw [var] at HEqe₀
        contradiction
      | lam =>
        have HEqe₀ := congrFun HEqe₀ Empty
        rw [app] at HEqe₀
        rw [lam] at HEqe₀
        contradiction
      | unit =>
        have HEqe₀ := congrFun HEqe₀ Empty
        rw [app] at HEqe₀
        rw [unit] at HEqe₀
        contradiction
    | _ => admit
