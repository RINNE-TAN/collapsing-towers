
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

theorem hasTy_mono : hasTy Γ e τ -> ok (Φ ++ Γ ++ Δ) -> hasTy (Φ ++ Γ ++ Δ) e τ :=
  by
  intro HhasTy HokΓ
  induction HhasTy generalizing Φ with
  | @hasTy_var Γ x _ HokΓ₀ Hlookup =>
    constructor
    apply HokΓ
    induction Γ generalizing Φ with
    | nil => simp at *
    | cons head tails IHtails =>
      simp at *
      admit
  | @hasTy_lam _ Γ _ _ L _
    IHhasTyE =>
    apply hasTy.hasTy_lam (L ∪ context_terms (Γ ++ Δ))
    intro x HnotInL
    simp at HnotInL
    admit
  | hasTy_app _ _ IHhasTyF IHhasTyArg =>
    constructor
    apply IHhasTyF
    apply HokΓ
    apply IHhasTyArg
    apply HokΓ
  | hasTy_unit => constructor

theorem pick_fresh (e : Expr) (L : Finset ℕ) : ∃ x, x ∉ (L ∪ fv e) := by apply Infinite.exists_not_mem_finset (L ∪ fv e)

theorem typing_regular : hasTy Γ e τ -> lc e := by
  intro HhasTyE
  induction HhasTyE with
  | hasTy_var => constructor
  | hasTy_lam L _ IHe =>
    constructor
    intro fresh
    intro Hfresh
    apply IHe
    apply Hfresh
  | hasTy_app _ _ IHf IHarg =>
    constructor
    apply IHf
    apply IHarg
  | hasTy_unit => constructor

theorem typing_subst_strengthened :
    hasTy Γ e τ₁ -> Γ = Δ ++ (z, τ₀) :: Φ -> hasTy Φ v τ₀ -> hasTy (Δ ++ Φ) (subst z v e) τ₁ :=
  by
  intro HhasTyE HEqΓ HhasTyV
  induction HhasTyE generalizing Δ with
  | @hasTy_var Γ x τ HokΓ Hlookup =>
    if HEqx : z = x then
      rw [HEqx]
      simp
      rw [← List.append_nil (Δ ++ Φ)]
      admit
    else
      simp
      rw [if_neg HEqx]
      admit
  | hasTy_app _ _ IHf IHarg =>
    simp
    constructor
    apply IHf
    apply HEqΓ
    apply IHarg
    apply HEqΓ
  | @hasTy_lam τ₁ _ e _ L _ IHe =>
    simp
    apply hasTy.hasTy_lam (L ∪ { z })
    intro fresh Hfresh
    simp at *
    rw [← subst_open_var]
    rw [← List.nil_append ((fresh, τ₁) :: (Δ ++ Φ)), List.append_cons, List.nil_append, ← List.append_assoc]
    apply IHe
    apply Hfresh.left
    rw [HEqΓ]
    simp
    intro HEqfresh
    apply Hfresh.right
    rw [HEqfresh]
    apply typing_regular
    apply HhasTyV
  | hasTy_unit => constructor

theorem typing_subst : hasTy ((z, τ₀) :: Φ) e τ₁ -> hasTy Φ v τ₀ -> hasTy Φ (subst z v e) τ₁ :=
  by
  intro HhasTyE HhasTyV
  rw [← List.nil_append Φ]
  apply typing_subst_strengthened
  apply HhasTyE
  rfl
  apply HhasTyV

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

theorem progress : hasTy [] e₀ τ -> value e₀ \/ ∃ e₁, step e₀ e₁ :=
  by
  generalize HEqΓ : [] = Γ
  intro HhasTye₀
  induction HhasTye₀ with
  | hasTy_app _ _ IHf IHarg =>
    right
    cases IHf HEqΓ with
    | inl HvalueF =>
      cases IHarg HEqΓ with
      | inl HvalueArg => admit
      | inr HstepArg => admit
    | inr HstepF =>
      cases IHarg HEqΓ with
      | inl HvalueArg => admit
      | inr HstepArg => admit
  | hasTy_unit =>
    left
    constructor
  | _ => admit
