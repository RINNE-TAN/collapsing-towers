
import Mathlib.Data.Finset.Basic
inductive Expr : Type where
  | bvar (i : Nat)
  | fvar (x : String)
  | lam (e : Expr)
  | app (f : Expr) (arg : Expr)
  | unit

@[simp]
def subst (x : String) (v : Expr) : Expr -> Expr
  | .bvar i => .bvar i
  | .fvar y => if x == y then v else .fvar y
  | .lam e => .lam (subst x v e)
  | .app f arg => .app (subst x v f) (subst x v arg)
  | .unit => .unit

@[simp]
def openRec (n : Nat) (v : Expr) : Expr -> Expr
  | .bvar i => if n == i then v else .bvar i
  | .fvar x => .fvar x
  | .lam e => .lam (openRec (n + 1) v e)
  | .app f arg => .app (openRec n v f) (openRec n v arg)
  | .unit => .unit

@[simp]
def open₀ (v : Expr) : Expr -> Expr :=
  openRec 0 v

inductive lc : Expr -> Prop where
  | lc_fvar : lc (.fvar x)
  | lc_lam : lc (open₀ e x) -> lc (.lam e)
  | lc_app : lc f -> lc arg -> lc (.app f arg)
  | lc_unit : lc .unit

inductive value : Expr -> Prop where
  | value_lam : value (.lam e)
  | value_unit : value .unit

abbrev Ctx :=
  Expr -> Expr

notation:max a "⟦" b "⟧" => a b

inductive ctx𝔹 : Ctx -> Prop where
  | ctx𝔹_appL : lc arg -> ctx𝔹 (fun X => .app X arg)
  | ctx𝔹_appR : value v -> ctx𝔹 (fun X => .app v X)

inductive ctx𝕄 : Ctx -> Prop where
  | ctx𝕄_hole : ctx𝕄 id
  | ctx𝕄_𝔹 : ctx𝔹 B -> ctx𝕄 M -> ctx𝕄 (B ∘ M)

inductive step : Expr -> Expr -> Prop where
  | step_appβ : ctx𝕄 M -> lc (.lam e) -> value v -> step M⟦.app (.lam e) v⟧ M⟦open₀ e v⟧

-- deterministic
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
  | @step_appβ M₀ e₀ v₀ HM₀ _ HV₀ =>
    generalize HEq : M₀⟦.app (.lam e₀) v₀⟧ = expr₀
    intros He₁e₂
    induction He₁e₂ with
    | @step_appβ M₁ e₁ v₁ HM₁ _ HV₁ =>
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
            have HV₀ : value (.lam e₀) := by constructor
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
            have HV₁ : value (.lam e₁) := by constructor
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
          have notV₀ : ¬value (M₀⟦.app (.lam e₀) v₀⟧) :=
            by
            apply ctx𝕄_not_value
            apply HM₀
            intro HV
            nomatch HV
          have notV₁ : ¬value (M₁⟦.app (.lam e₁) v₁⟧) :=
            by
            apply ctx𝕄_not_value
            apply HM₁
            intro HV
            nomatch HV
          have HEq := ctx𝔹_eq HB₀ HB₁ notV₀ notV₁ HEq
          rw [HEq.left]
          have HEq := IHM₀ HM₁ HEq.right
          rw [HEq]

-- typing
inductive Ty : Type where
  | ty_unit
  | ty_fun : Ty -> Ty -> Ty

abbrev TyCtx :=
  List (String × Ty)

@[simp]
def lookup (Γ : TyCtx) (x : String) : Option Ty :=
  match Γ with
  | [] => none
  | (y, τ) :: Γ => if x = y then some τ else lookup Γ x

@[simp]
def in_context (x : String) : TyCtx → Prop
  | [] => False
  | ((y, _) :: Γ) => (x = y) ∨ (in_context x Γ)

@[simp]
def context_terms : TyCtx → (Finset String)
  | [] => ∅
  | ((x, _) :: Γ) => { x } ∪ (context_terms Γ)

inductive ok : TyCtx → Prop where
  | ok_nil : ok []
  | ok_cons : ok Γ → ¬(in_context x Γ) → ok ((x, τ) :: Γ)

inductive hasTy : TyCtx -> Expr -> Ty -> Prop
  | hasTy_var : ok Γ -> lookup Γ x = some τ -> hasTy Γ (.fvar x) τ
  |
  hasTy_lam :
    (L : Finset String) ->
      (∀ x, x ∉ L -> hasTy ((x, τ₀) :: Γ) (open₀ (.fvar x) e) τ₁) -> hasTy Γ (.lam e) (.ty_fun τ₀ τ₁)
  | hasTy_app : hasTy Γ f (.ty_fun τ₀ τ₁) -> hasTy Γ arg τ₀ -> hasTy Γ (.app f arg) τ₁
  | hasTy_unit : hasTy Γ .unit .ty_unit

theorem context_terms_iff_in_list : x ∈ context_terms Γ ↔ in_context x Γ :=
  by
  induction Γ
  case nil => simp
  case cons _ _ IH =>
    simp
    rw [IH]

theorem hasTy_mono : hasTy Γ₀ e τ -> ok (Γ₀ ++ Γ₁) -> hasTy (Γ₀ ++ Γ₁) e τ :=
  by
  intro HhasTy HokΓ
  induction HhasTy with
  | @hasTy_var Γ₀ x _ HokΓ₀ Hlookup =>
    constructor
    apply HokΓ
    induction Γ₀ with
    | nil => simp at *
    | cons head tails IHtails =>
      simp at *
      if HEq : x = head.fst then
        rw [HEq] at Hlookup
        rw [HEq]
        simp at *
        apply Hlookup
      else
        cases HokΓ₀ with
        | ok_cons HokTailsΓ₀ =>
          cases HokΓ with
          | ok_cons HokTailsΓ =>
            rw [if_neg HEq] at Hlookup
            rw [if_neg HEq]
            apply IHtails
            apply HokTailsΓ₀
            apply Hlookup
            apply HokTailsΓ
  | @hasTy_lam _ Γ₀ _ _ L _
    IHhasTyE =>
    apply hasTy.hasTy_lam (L ∪ context_terms (Γ₀ ++ Γ₁))
    intro x HnotInL
    simp at HnotInL
    apply IHhasTyE
    apply HnotInL.left
    constructor
    apply HokΓ
    intro HinΓ
    apply HnotInL.right
    apply (context_terms_iff_in_list.mpr)
    apply HinΓ
  | hasTy_app _ _ IHhasTyF IHhasTyArg =>
    constructor
    apply IHhasTyF
    apply HokΓ
    apply IHhasTyArg
    apply HokΓ
  | hasTy_unit => constructor

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
        | hasTy_lam =>
          simp at *
          admit
    | ctx𝕄_𝔹 => admit
