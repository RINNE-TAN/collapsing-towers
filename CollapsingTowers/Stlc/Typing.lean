
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

theorem typing_subst : hasTy ((x, τ₀) :: Γ) e τ₁ -> hasTy Γ v τ₀ -> hasTy Γ (subst x v e) τ₁ :=
  by
  generalize EqΓ : (x, τ₀) :: Γ = Γ₁
  intros HhasTyE HhasTyV
  induction HhasTyE with
  | hasTy_lam L _ IHhasTyE =>
    simp at *
    constructor
    admit
    admit
  | _ => admit

theorem typing_ctx𝔹 : ctx𝔹 B -> (∀ τ₀, hasTy [] e₀ τ₀ -> hasTy [] e₁ τ₀) -> hasTy [] (B e₀) τ₁ -> hasTy [] (B e₁) τ₁ :=
  by
  intro HB HhasTyHead HhasTyB
  induction HB with
  | ctx𝔹_appL Hlc =>
    cases HhasTyB with
    | hasTy_app HhasTyF HhasTyArg =>
      constructor
      apply HhasTyHead
      apply HhasTyF
      apply HhasTyArg
  | ctx𝔹_appR HValue =>
    cases HhasTyB with
    | hasTy_app HhasTyF HhasTyArg =>
      simp at *
      constructor
      apply HhasTyF
      apply HhasTyHead
      apply HhasTyArg

theorem preservation : step e₀ e₁ -> hasTy [] e₀ τ -> hasTy [] e₁ τ :=
  by
  intro Hstep
  cases Hstep with
  | @step_appβ _ e v HM Hlc HV =>
    clear Hlc
    induction HM generalizing τ with
    | ctx𝕄_hole =>
      intro HhasTyApp
      cases HhasTyApp with
      | hasTy_app HhasTyLam hasTyV =>
        cases HhasTyLam with
        | hasTy_lam L HhasTyE =>
          obtain ⟨fresh, Hfresh⟩ := pick_fresh e L
          simp at Hfresh
          have HEq : subst fresh v (open₀ (Expr.fvar fresh) e) = open₀ v e := subst_intro Hfresh.right
          rw [← HEq]
          apply typing_subst (HhasTyE fresh Hfresh.left) hasTyV
    | ctx𝕄_𝔹 HB _ IHHasTyM =>
      simp at *
      apply typing_ctx𝔹
      apply HB
      apply IHHasTyM
