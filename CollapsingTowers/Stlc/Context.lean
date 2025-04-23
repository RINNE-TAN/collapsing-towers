
import CollapsingTowers.Stlc.Basic
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

theorem context_terms_iff_in_list : x ∈ context_terms Γ ↔ in_context x Γ :=
  by
  induction Γ
  case nil => simp
  case cons _ _ IH =>
    simp
    rw [IH]

theorem in_context_extend : in_context x (Φ ++ Δ) -> in_context x (Φ ++ Ψ ++ Δ) := by
  induction Φ with
  | nil =>
    simp
    induction Ψ with
    | nil => simp
    | cons _ _ IHtailsΨ =>
      intro HinΔ
      simp
      right
      apply IHtailsΨ
      apply HinΔ
  | cons _ _ IHtailsΦ =>
    intro HinΦΔ
    simp at *
    cases HinΦΔ with
    | inl HEqx =>
      left
      apply HEqx
    | inr HintailsΦΔ =>
      right
      apply IHtailsΦ
      apply HintailsΦΔ

theorem ok_shrink : ok (Φ ++ Ψ ++ Δ) -> ok (Φ ++ Δ) := by
  induction Φ with
  | nil =>
    simp
    induction Ψ with
    | nil => simp
    | cons _ _ IHtailsΨ =>
      intro HokΨ
      apply IHtailsΨ
      cases HokΨ with
      | ok_cons HoktailsΨ => apply HoktailsΨ
  | cons _ _ IHtailsΦ =>
    intro HokΦ
    cases HokΦ with
    | ok_cons HoktailsΦ HnotIntailsΦ =>
      constructor
      apply IHtailsΦ
      apply HoktailsΦ
      intro HIntailsΦ
      apply HnotIntailsΦ
      apply in_context_extend
      apply HIntailsΦ

theorem lookup_shrink : lookup (Φ ++ [(y, τ₁)] ++ Δ) x = some τ₀ -> x ≠ y -> lookup (Φ ++ Δ) x = some τ₀ :=
  by
  intro Hlookup HNe
  induction Φ with
  | nil =>
    simp at *
    rw [if_neg HNe] at Hlookup
    apply Hlookup
  | cons head _ IHlookup =>
    if HEqx : x = head.fst then
      rw [HEqx]
      rw [HEqx] at Hlookup
      simp at *
      apply Hlookup
    else
      simp at *
      rw [if_neg HEqx]
      rw [if_neg HEqx] at Hlookup
      apply IHlookup
      apply Hlookup

theorem lookup_in_context : lookup Γ x = some τ -> in_context x Γ :=
  by
  intro Hlookup
  induction Γ with
  | nil => nomatch Hlookup
  | cons head _ IHlookup =>
    if HEqx : x = head.fst then
      left
      apply HEqx
    else
      right
      apply IHlookup
      simp at Hlookup
      rw [if_neg HEqx] at Hlookup
      apply Hlookup

theorem lookup_extend : lookup (Φ ++ Δ) x = some τ -> ok (Φ ++ Ψ ++ Δ) -> lookup (Φ ++ Ψ ++ Δ) x = some τ :=
  by
  intro Hlookup Hok
  induction Φ with
  | nil =>
    simp at *
    induction Ψ with
    | nil => apply Hlookup
    | cons head tails IHtailsΨ =>
      if HEqx : x = head.fst then
        exfalso
        rw [List.cons_append] at Hok
        cases Hok with
        | ok_cons HoktailsΨ HnotIntailsΨ =>
          apply HnotIntailsΨ
          rw [← List.nil_append tails]
          apply in_context_extend
          apply lookup_in_context
          simp at *
          rw [← HEqx]
          apply Hlookup
      else
        simp
        rw [if_neg HEqx]
        apply IHtailsΨ
        cases Hok with
        | ok_cons HoktailsΨ => apply HoktailsΨ
  | cons head tails IHtailsΦ =>
    if HEqx : x = head.fst then
      rw [HEqx]
      rw [HEqx] at Hlookup
      simp at *
      apply Hlookup
    else
      simp at *
      rw [if_neg HEqx]
      rw [if_neg HEqx] at Hlookup
      apply IHtailsΦ
      apply Hlookup
      cases Hok with
      | ok_cons HoktailsΦ => apply HoktailsΦ
