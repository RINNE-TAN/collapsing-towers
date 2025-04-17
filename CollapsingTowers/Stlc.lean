
inductive Expr : Type where
  | Var (x : Nat)
  | Lam (e : Expr)
  | App (f : Expr) (arg : Expr)
  | Unit

inductive value : Expr -> Prop where
  | value_lam : value (.Lam e)
  | value_unit : value .Unit

abbrev Ctx :=
  Expr -> Expr

notation:max a "⟦" b "⟧" => a b

inductive ctx𝔹 : Ctx -> Prop where
  | ctx𝔹_appL : ctx𝔹 (fun X => .App X arg)
  | ctx𝔹_appR : value v -> ctx𝔹 (fun X => .App v X)

inductive ctx𝕄 : Ctx -> Prop where
  | ctx𝕄_hole : ctx𝕄 id
  | ctx𝕄_𝔹 : ctx𝔹 B -> ctx𝕄 M -> ctx𝕄 (B ∘ M)

@[simp]
def subst (n : Nat) (v : Expr) (e : Expr) : Expr :=
  match e with
  | .Var x => if x == n then v else if x > n then .Var (x - 1) else .Var x
  | .Lam e => .Lam (subst (n + 1) v e)
  | .App f arg => .App (subst n v f) (subst n v arg)
  | .Unit => .Unit

inductive step : Expr -> Expr -> Prop where
  | step_appβ : ctx𝕄 M -> value v -> step M⟦.App (.Lam e) v⟧ M⟦subst 0 v e⟧

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
      rw [HEq.left, HEq.right]
      constructor
      rfl
      rfl
    | ctx𝔹_appR HV =>
      simp at HEq
      exfalso
      apply HnotV₀
      rw [HEq.left]
      apply HV
  | ctx𝔹_appR HV =>
    simp at HEq
    induction HB₁ with
    | ctx𝔹_appL =>
      simp at HEq
      exfalso
      apply HnotV₁
      rw [← HEq.left]
      apply HV
    | ctx𝔹_appR HV =>
      simp at HEq
      rw [HEq.left, HEq.right]
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
  | @step_appβ M₀ v₀ e₀ HM₀ HV₀ =>
    generalize HEq : M₀⟦.App (.Lam e₀) v₀⟧ = expr₀
    intros He₁e₂
    induction He₁e₂ with
    | @step_appβ M₁ v₁ e₁ HM₁ HV₁ =>
      induction HM₀ generalizing M₁ with
      | ctx𝕄_hole =>
        cases HM₁ with
        | ctx𝕄_hole =>
          simp at *
          rw [HEq.left, HEq.right]
        | ctx𝕄_𝔹 HB HM₁ =>
          cases HB with
          | ctx𝔹_appL =>
            simp at *
            have HV₀ : value (.Lam e₀) := by constructor
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
            have HV₁ : value (.Lam e₁) := by constructor
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
          have notV₀ : ¬value (M₀⟦.App (.Lam e₀) v₀⟧) :=
            by
            apply ctx𝕄_not_value
            apply HM₀
            intro HV
            nomatch HV
          have notV₁ : ¬value (M₁⟦.App (.Lam e₁) v₁⟧) :=
            by
            apply ctx𝕄_not_value
            apply HM₁
            intro HV
            nomatch HV
          have HEq := ctx𝔹_eq HB₀ HB₁ notV₀ notV₁ HEq
          rw [HEq.left]
          have HEq := IHM₀ HM₁ HEq.right
          rw [HEq]

inductive Ty : Type where
  | ty_unit
  | ty_fun : Ty -> Ty -> Ty

abbrev TyCtx :=
  List Ty

inductive hasTy : TyCtx -> Expr -> Ty -> Prop
  | hasTy_var : Γ[x]? = some τ -> hasTy Γ (.Var x) τ
  | hasTy_lam : hasTy (τ₀ :: Γ) e τ₁ -> hasTy Γ (.Lam e) (.ty_fun τ₀ τ₁)
  | hasTy_app : hasTy Γ f (.ty_fun τ₀ τ₁) -> hasTy Γ arg τ₀ -> hasTy Γ (.App f arg) τ₁
  | hasTy_unit : hasTy Γ .Unit .ty_unit

theorem subst_hasTy : hasTy [] v τ₀ -> hasTy (τ₀ :: Γ) e τ₁ -> hasTy Γ (subst 0 v e) τ₁ :=
  by
  intros HhasTyV HhasTyE
  cases HhasTyE with
  | @hasTy_var _ x _ Hlookup =>
    cases x with
    | zero =>
      simp at *
      rw [← Hlookup]
      admit
    | succ =>
      simp at *
      constructor
      apply Hlookup
  | hasTy_lam => admit
  | hasTy_app => admit
  | hasTy_unit => admit

theorem preservation : step e₀ e₁ -> hasTy [] e₀ τ -> hasTy [] e₁ τ :=
  by
  intro Hstep
  cases Hstep with
  | step_appβ HM HV =>
    induction HM with
    | ctx𝕄_hole =>
      simp
      intro HhasTy
      cases HhasTy with
      | hasTy_app HhasTyF HhasTyArg =>
        cases HhasTyF with
        | hasTy_lam => admit
    | ctx𝕄_𝔹 => admit
