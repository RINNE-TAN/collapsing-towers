
import Mathlib.Data.Finset.Basic
import CollapsingTowers.Stlc.Basic
import CollapsingTowers.Stlc.OpenClose
import CollapsingTowers.Stlc.SmallStep
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
