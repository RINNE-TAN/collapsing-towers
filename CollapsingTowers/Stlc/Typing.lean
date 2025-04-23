
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.EquivFin
import CollapsingTowers.Stlc.Basic
import CollapsingTowers.Stlc.OpenClose
import CollapsingTowers.Stlc.SmallStep
import CollapsingTowers.Stlc.Context
inductive hasTy : TyCtx -> Expr -> Ty -> Prop
  | hasTy_var : ok Γ -> lookup Γ x = some τ -> hasTy Γ (.fvar x) τ
  |
  hasTy_lam :
    (L : Finset ℕ) -> (∀ x, x ∉ L -> hasTy ((x, τ₀) :: Γ) (open₀ (.fvar x) e) τ₁) -> hasTy Γ (.lam e) (.ty_fun τ₀ τ₁)
  | hasTy_app : hasTy Γ f (.ty_fun τ₀ τ₁) -> hasTy Γ arg τ₀ -> hasTy Γ (.app f arg) τ₁
  | hasTy_unit : hasTy Γ .unit .ty_unit

@[simp]
def stuck (e₀ : Expr) : Prop :=
  ¬(∃ e₁, step e₀ e₁) /\ ¬value e₀

theorem hasTy_mono : hasTy Γ e τ -> Γ = Φ ++ Δ -> ok (Φ ++ Ψ ++ Δ) -> hasTy (Φ ++ Ψ ++ Δ) e τ :=
  by
  intro HhasTy HEqΓ Hok
  induction HhasTy generalizing Φ with
  | hasTy_var HokLocal Hlookup =>
    constructor
    apply Hok
    apply lookup_extend
    rw [← HEqΓ]
    apply Hlookup
    apply Hok
  | hasTy_lam L _ IHe =>
    apply hasTy.hasTy_lam (L ∪ context_terms (Φ ++ Ψ ++ Δ))
    intro fresh Hfresh
    simp at Hfresh
    rw [← List.cons_append, ← List.cons_append]
    apply IHe
    apply Hfresh.left
    simp
    apply HEqΓ
    constructor
    apply Hok
    intro HInΓ
    apply Hfresh.right
    apply context_terms_iff_in_list.mpr
    simp at HInΓ
    apply HInΓ
  | hasTy_app _ _ IHf IHarg =>
    constructor
    apply IHf
    apply HEqΓ
    apply Hok
    apply IHarg
    apply HEqΓ
    apply Hok
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
      rw [← HEqx]
      rw [← HEqx] at Hlookup
      have HlookupEq : lookup Γ z = some τ₀ := by
        rw [HEqΓ]
        rw [← List.nil_append Δ]
        apply lookup_extend
        simp
        simp
        rw [← HEqΓ]
        apply HokΓ
      rw [List.append_cons] at HEqΓ
      rw [HEqΓ] at HokΓ
      rw [Hlookup] at HlookupEq
      simp at HlookupEq
      rw [HlookupEq]
      simp
      rw [← List.append_nil Δ]
      apply @hasTy_mono (Δ ++ Φ)
      rw [← List.nil_append Δ]
      apply hasTy_mono
      apply HhasTyV
      rfl
      simp
      apply ok_shrink
      apply HokΓ
      rfl
      simp
      apply ok_shrink
      apply HokΓ
    else
      simp
      rw [if_neg HEqx]
      rw [List.append_cons] at HEqΓ
      rw [HEqΓ] at HokΓ
      rw [HEqΓ] at Hlookup
      constructor
      apply ok_shrink
      apply HokΓ
      apply lookup_shrink
      apply Hlookup
      intro HEq
      apply HEqx
      rw [HEq]
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

theorem multi_preservation : multi e₀ e₁ -> hasTy [] e₀ τ -> hasTy [] e₁ τ :=
  by
  intro Hmulti HhasTye₀
  induction Hmulti with
  | multi_stop => apply HhasTye₀
  | multi_step Hstep _ IHHasTy =>
    apply IHHasTy
    apply preservation
    apply Hstep
    apply HhasTye₀

theorem progress : hasTy [] e₀ τ -> value e₀ \/ ∃ e₁, step e₀ e₁ :=
  by
  generalize HEqΓ : [] = Γ
  intro HhasTye₀
  induction HhasTye₀ with
  | hasTy_var Hok Hlookup =>
    rw [← HEqΓ] at Hlookup
    contradiction
  | hasTy_lam L HhasTyE =>
    left
    constructor
    constructor
    intro fresh Hfresh
    apply typing_regular
    apply HhasTyE fresh Hfresh
  | @hasTy_app _ f₀ _ _ arg₀ HhasTyF HhasTyArg IHf IHarg =>
    right
    cases IHf HEqΓ with
    | inl HvalueF =>
      cases IHarg HEqΓ with
      | inl HvalueArg =>
        cases HvalueF with
        | value_lam Hlc =>
          constructor
          apply (step.step_appβ ctx𝕄.ctx𝕄_hole)
          apply Hlc
          apply HvalueArg
        | value_unit => nomatch HhasTyF
      | inr HstepArg =>
        obtain ⟨arg₁, HstepArg⟩ := HstepArg
        constructor
        apply step_in_ctx𝔹 (ctx𝔹.ctx𝔹_appR _)
        apply HstepArg
        apply HvalueF
    | inr HstepF =>
      cases IHarg HEqΓ with
      | inl HvalueArg =>
        obtain ⟨f₁, HstepF⟩ := HstepF
        constructor
        apply step_in_ctx𝔹 (ctx𝔹.ctx𝔹_appL _)
        apply HstepF
        apply value_lc
        apply HvalueArg
      | inr =>
        obtain ⟨f₁, HstepF⟩ := HstepF
        constructor
        apply step_in_ctx𝔹 (ctx𝔹.ctx𝔹_appL _)
        apply HstepF
        apply typing_regular
        apply HhasTyArg
  | hasTy_unit =>
    left
    constructor

theorem soundness : multi e₀ e₁ -> hasTy [] e₀ τ -> ¬stuck e₁ :=
  by
  intro Hmulti HhasTye₀
  simp
  intro HNstep
  cases progress (multi_preservation Hmulti HhasTye₀) with
  | inl HV => apply HV
  | inr Hstep =>
    obtain ⟨e₂, Hstep⟩ := Hstep
    have HNstep := HNstep e₂
    contradiction
