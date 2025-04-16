
inductive Expr : Type where
  | Var (x : String)
  | Lam (x : String) (e : Expr)
  | App (f : Expr) (arg : Expr)

inductive value : Expr -> Prop where
  | value_lam : value (.Lam x e)

abbrev Ctx :=
  Expr -> Expr

notation:max a "⟦" b "⟧" => a b

inductive ctx𝔹 : Ctx -> Prop where
  | ctx𝔹_appL : ctx𝔹 (fun X => .App X arg)
  | ctx𝔹_appR : value v -> ctx𝔹 (fun X => .App v X)

inductive ctx𝕄 : Ctx -> Prop where
  | ctx𝕄_hole : ctx𝕄 id
  | ctx𝕄_𝔹 : ctx𝔹 B -> ctx𝕄 M -> ctx𝕄 (B ∘ M)

def subst (x : String) (v : Expr) (e : Expr) : Expr :=
  match e with
  | .Var y => if x == y then v else .Var y
  | .Lam y e => if x == y then .Lam y e else .Lam y (subst x v e)
  | .App f arg => .App (subst x v f) (subst x v arg)

inductive step : Expr -> Expr -> Prop where
  | step_appβ : ctx𝕄 M -> value v -> step M⟦.App (.Lam x e) v⟧ M⟦subst x v e⟧

theorem ctx𝔹_not_value : ctx𝔹 B -> ¬value B⟦e⟧ := by
  intros HB Hvalue
  induction HB with
  | _ =>
    simp at Hvalue
    nomatch Hvalue

theorem ctx𝔹_eq : ctx𝔹 B₀ -> ctx𝔹 B₁ -> ¬value e₀ -> ¬value e₁ -> B₀⟦e₀⟧ = B₁⟦e₁⟧ -> e₀ = e₁ :=
  by
  intros HB₀ HB₁ HnotV₀ HnotV₁ HEq
  induction HB₀ with
  | ctx𝔹_appL =>
    simp at HEq
    induction HB₁ with
    | ctx𝔹_appL =>
      simp at HEq
      apply (And.left HEq)
    | ctx𝔹_appR HV =>
      simp at HEq
      exfalso
      apply HnotV₀
      rw [And.left HEq]
      apply HV
  | ctx𝔹_appR HV =>
    simp at HEq
    induction HB₁ with
    | ctx𝔹_appL =>
      simp at HEq
      exfalso
      apply HnotV₁
      rw [← And.left HEq]
      apply HV
    | ctx𝔹_appR HV =>
      simp at HEq
      apply (And.right HEq)

theorem ctx𝕄_value : ctx𝕄 M -> value M⟦e⟧ -> M = id :=
  by
  intros HM Hvalue
  induction HM with
  | ctx𝕄_hole => rfl
  | ctx𝕄_𝔹 HB =>
    exfalso
    apply ctx𝔹_not_value
    apply HB
    apply Hvalue

theorem step_deterministic : step expr₀ expr₁ -> step expr₀ expr₂ -> expr₁ = expr₂ :=
  by
  intros He₀e₁
  induction He₀e₁ with
  | @step_appβ M₀ v₀ x₀ e₀ HM₀ HV₀ =>
    generalize HEq : M₀⟦.App (.Lam x₀ e₀) v₀⟧ = expr₀
    intros He₁e₂
    induction He₁e₂ with
    | @step_appβ M₁ v₁ x₁ e₁ HM₁ HV₁ =>
      induction HM₀ generalizing M₁ with
      | ctx𝕄_hole =>
        cases HM₁ with
        | ctx𝕄_hole =>
          simp at *
          rw [And.left (And.left HEq), And.right (And.left HEq), And.right HEq]
        | ctx𝕄_𝔹 HB HM₁ =>
          cases HB with
          | ctx𝔹_appL =>
            simp at *
            exfalso
            admit
          | ctx𝔹_appR =>
            simp at *
            admit
      | ctx𝕄_𝔹 HB HM₀ ihM₀ =>
        cases HM₁ with
        | ctx𝕄_hole =>
          cases HB with
          | ctx𝔹_appL =>
            simp at *
            exfalso
            admit
          | ctx𝔹_appR =>
            simp at *
            admit
        | ctx𝕄_𝔹 HB HM₁ =>
          simp at *
          admit
