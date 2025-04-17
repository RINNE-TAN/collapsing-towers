
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

theorem ctx𝔹_eq : ctx𝔹 B₀ -> ctx𝔹 B₁ -> ¬value e₀ -> ¬value e₁ -> B₀⟦e₀⟧ = B₁⟦e₁⟧ -> B₀ = B₁ /\ e₀ = e₁ :=
  by
  intros HB₀ HB₁ HnotV₀ HnotV₁ HEq
  induction HB₀ with
  | ctx𝔹_appL =>
    simp at HEq
    induction HB₁ with
    | ctx𝔹_appL =>
      simp at HEq
      rw [And.left HEq, And.right HEq]
      constructor
      rfl
      rfl
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
      rw [And.left HEq, And.right HEq]
      constructor
      rfl
      rfl

theorem ctx𝕄_value : ctx𝕄 M -> value M⟦e⟧ -> M = id /\ value e :=
  by
  intros HM Hvalue
  induction HM with
  | ctx𝕄_hole =>
    constructor
    rfl
    apply Hvalue
  | ctx𝕄_𝔹 HB =>
    exfalso
    apply ctx𝔹_not_value
    apply HB
    apply Hvalue

theorem ctx𝕄_not_value : ctx𝕄 M -> ¬value e -> ¬value M⟦e⟧ :=
  by
  intros HM HnotV HMv
  apply HnotV
  have HId := ctx𝕄_value HM HMv
  apply HId.right

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
          rw [HEq.left.left, HEq.left.right, HEq.right]
        | ctx𝕄_𝔹 HB HM₁ =>
          cases HB with
          | ctx𝔹_appL =>
            simp at *
            have HV₀ : value (.Lam x₀ e₀) := by constructor
            rw [HEq.left] at HV₀
            have HId := ctx𝕄_value HM₁ HV₀
            rw [HId.left] at HV₀
            nomatch HV₀
          | ctx𝔹_appR =>
            simp at *
            rw [HEq.right] at HV₀
            have HId := ctx𝕄_value HM₁ HV₀
            rw [HId.left] at HV₀
            nomatch HV₀
      | @ctx𝕄_𝔹 _ M₀ HB₀ HM₀ IHM₀ =>
        cases HM₁ with
        | ctx𝕄_hole =>
          cases HB₀ with
          | ctx𝔹_appL =>
            simp at *
            have HV₁ : value (.Lam x₁ e₁) := by constructor
            rw [← HEq.left] at HV₁
            have HId := ctx𝕄_value HM₀ HV₁
            rw [HId.left] at HV₁
            nomatch HV₁
          | ctx𝔹_appR =>
            simp at *
            rw [← HEq.right] at HV₁
            have HId := ctx𝕄_value HM₀ HV₁
            rw [HId.left] at HV₁
            nomatch HV₁
        | @ctx𝕄_𝔹 _ M₁ HB₁ HM₁ =>
          simp at *
          have notV₀ : ¬value (M₀⟦.App (.Lam x₀ e₀) v₀⟧) :=
            by
            apply ctx𝕄_not_value
            apply HM₀
            intro HV
            nomatch HV
          have notV₁ : ¬value (M₁⟦.App (.Lam x₁ e₁) v₁⟧) :=
            by
            apply ctx𝕄_not_value
            apply HM₁
            intro HV
            nomatch HV
          have HEq := ctx𝔹_eq HB₀ HB₁ notV₀ notV₁ HEq
          rw [HEq.left]
          have HEq := IHM₀ HM₁ HEq.right
          rw [HEq]
