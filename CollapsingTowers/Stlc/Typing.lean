
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.EquivFin
import CollapsingTowers.Stlc.Basic
import CollapsingTowers.Stlc.OpenClose
import CollapsingTowers.Stlc.SmallStep
inductive Ty : Type where
  | ty_unit
  | ty_fun : Ty -> Ty -> Ty

abbrev TyCtx :=
  List (ℕ × Ty)

@[simp]
def lookup (Γ : TyCtx) (x : ℕ) : Option Ty :=
  match Γ with
  | [] => none
  | (y, τ) :: Γ => if x = y then some τ else lookup Γ x

@[simp]
def in_context (x : ℕ) : TyCtx → Prop
  | [] => False
  | ((y, _) :: Γ) => (x = y) ∨ (in_context x Γ)

@[simp]
def context_terms : TyCtx → (Finset ℕ)
  | [] => ∅
  | ((x, _) :: Γ) => { x } ∪ (context_terms Γ)

inductive ok : TyCtx → Prop where
  | ok_nil : ok []
  | ok_cons : ok Γ → ¬(in_context x Γ) → ok ((x, τ) :: Γ)

inductive hasTy : TyCtx -> Expr -> Ty -> Prop
  | hasTy_var : ok Γ -> lookup Γ x = some τ -> hasTy Γ (.fvar x) τ
  |
  hasTy_lam :
    (L : Finset ℕ) -> (∀ x, x ∉ L -> hasTy ((x, τ₀) :: Γ) (open₀ (.fvar x) e) τ₁) -> hasTy Γ (.lam e) (.ty_fun τ₀ τ₁)
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

theorem pick_fresh (e : Expr) (L : Finset ℕ) : ∃ x, x ∉ (L ∪ fv e) := by apply Infinite.exists_not_mem_finset (L ∪ fv e)

theorem hasTy_fresh :
    fresh ∉ fv e -> hasTy [] v τ₀ -> hasTy [(fresh, τ₀)] (open₀ (Expr.fvar fresh) e) τ₁ -> hasTy [] (open₀ v e) τ₁ :=
  by
  intro Hfresh HhasTyV HhasTyOpen
  admit

theorem preservation : step e₀ e₁ -> hasTy [] e₀ τ -> hasTy [] e₁ τ :=
  by
  intro Hstep
  cases Hstep with
  | @step_appβ _ e _ HM Hlc HV =>
    induction HM with
    | ctx𝕄_hole =>
      intro HhasTy
      cases HhasTy with
      | hasTy_app HhasTyBody HhasTyV =>
        cases HhasTyBody with
        | hasTy_lam L HhasTyE =>
          obtain ⟨fresh, Hfresh⟩ := pick_fresh e L
          simp at Hfresh
          have HhasTyE := HhasTyE fresh Hfresh.left
          admit
    | ctx𝕄_𝔹 => admit
