
import Mathlib.Data.Nat.Basic
import CollapsingTowers.TwoLevelFull.Syntax
@[simp]
def getr {α : Type} (x : ℕ) (l : List α) : Option α :=
  match l with
  | [] => none
  | head :: tails => if tails.length == x then some head else getr x tails

@[simp]
def setr {α : Type} (x : ℕ) (a : α) (l : List α) : Option (List α) :=
  match l with
  | [] => none
  | head :: tails =>
    if tails.length == x then some (a :: tails)
    else do
      let tails ← setr x a tails
      (head :: tails)

theorem getr_iff_lt : ∀ {α : Type} (l : List α) i, i < l.length ↔ ∃ a, getr i l = some a :=
  by
  intro α l i; constructor
  . intro H; induction l
    case nil => nomatch H
    case cons tails IH =>
      simp; by_cases HEq : tails.length = i
      . simp [HEq]
      . simp [if_neg HEq]; apply IH; simp at H; omega
  . intro H; induction l
    case nil => nomatch H
    case cons tails IH =>
      simp at H; by_cases HEq : tails.length = i
      . subst HEq; simp
      . simp [if_neg HEq] at H; simp
        have _ := IH H; omega

theorem setr_iff_lt : ∀ {α : Type} (l₀ : List α) i a, i < l₀.length ↔ ∃ l₁, setr i a l₀ = some l₁ :=
  by
  intro α l₀ i a; constructor
  . intro H; induction l₀
    case nil => nomatch H
    case cons head tails IH =>
      simp; by_cases HEq : tails.length = i
      . simp [HEq]
      . simp [if_neg HEq]
        have ⟨l₁, Hpatch⟩ : ∃ l₁, setr i a tails = some l₁ :=
          by apply IH; simp at H; omega
        exists head :: l₁; rw [Hpatch]; simp
  . intro H; induction l₀
    case nil => nomatch H
    case cons head tails IH =>
      simp at H; by_cases HEq : tails.length = i
      . subst HEq; simp
      . simp [if_neg HEq] at H; simp
        have _ : i < tails.length :=
          by
          apply IH
          have ⟨l₁, Hpatch⟩ := H
          generalize HEq : setr i a tails = tailRes
          cases tailRes
          case none => rw [HEq] at Hpatch; nomatch Hpatch
          case some l₁ => exists l₁
        omega

@[simp]
def binds {α : Type} (x : ℕ) (a : α) (l : List α) :=
  getr x l = some a

@[simp]
def patch {α : Type} (x : ℕ) (a : α) (l₀ : List α) (l₁ : List α) :=
  setr x a l₀ = some l₁

theorem binds_extend : ∀ {α : Type} Γ Δ x (a : α), binds x a Γ → binds x a (Δ ++ Γ) :=
  by
  intros _ Γ Δ x a Hbinds
  induction Δ with
  | nil => apply Hbinds
  | cons head tails IHtails =>
    simp
    by_cases Hx : tails.length + Γ.length = x
    . have Hx : x < Γ.length := by apply (getr_iff_lt _ _).mpr; exists a
      omega
    . rw [if_neg Hx]; apply IHtails

theorem binds_extendr : ∀ {α : Type} Γ Δ x (a : α), binds x a Γ → binds (x + Δ.length) a (Γ ++ Δ) :=
  by
  intros _ Γ Δ x a
  induction Γ with
  | nil => simp
  | cons head tails IHtails =>
    simp
    by_cases HEq : tails.length = x
    . repeat rw [if_pos HEq]; simp
    . repeat rw [if_neg HEq]
      apply IHtails

theorem binds_shrink : ∀ {α : Type} Γ Δ x (a : α), x < Γ.length → binds x a (Δ ++ Γ) → binds x a Γ :=
  by
  intros _ Γ Δ x a HLt
  induction Δ with
  | nil => simp
  | cons head tails IHtails =>
    intro Hbinds; apply IHtails
    simp at *
    have HNe : tails.length + Γ.length ≠ x := by omega
    rw [if_neg HNe] at Hbinds
    apply Hbinds

theorem binds_shrinkr : ∀ {α : Type} Γ Δ x (a : α), binds (x + Δ.length) a (Γ ++ Δ) → binds x a Γ :=
  by
  intros _ Γ Δ x a
  induction Γ with
  | nil =>
    simp; intro Hgetr
    have : x + Δ.length < Δ.length := by apply (getr_iff_lt _ _).mpr; exists a
    omega
  | cons head tails IHtails =>
    simp
    by_cases HEq : tails.length = x
    . repeat rw [if_pos HEq]; simp
    . repeat rw [if_neg HEq]
      apply IHtails

theorem binds_deterministic :
  ∀ {α : Type} x (a b : α) l,
    binds x a l →
    binds x b l →
    a = b :=
  by
  intros _ x a b l Hbinds₀ Hbinds₁
  simp at Hbinds₀ Hbinds₁
  simp [Hbinds₀] at Hbinds₁
  assumption

theorem length_patch :
  ∀ {α : Type} x (a : α) l₀ l₁,
    patch x a l₀ l₁ →
    l₀.length = l₁.length :=
  by
  intro _ x a l₀ l₁ Hpatch
  induction l₀ generalizing l₁ with
  | nil => nomatch Hpatch
  | cons head₀ tails₀ IHtails =>
    simp at Hpatch
    by_cases HEq : tails₀.length = x
    . simp [if_pos HEq] at Hpatch
      rw [← Hpatch]; rfl
    . simp [if_neg HEq] at Hpatch
      generalize HEq : setr x a tails₀ = tailRes
      cases tailRes with
      | none => simp [HEq] at Hpatch
      | some tails₁ =>
        simp [HEq] at Hpatch; simp [← Hpatch]
        apply IHtails; apply HEq

theorem patch_binds :
  ∀ {α : Type} x (a : α) l₀ l₁,
    patch x a l₀ l₁ →
    binds x a l₁ :=
  by
  intros _ x a l₀ l₁ Hpatch
  induction l₀ generalizing l₁ with
  | nil => nomatch Hpatch
  | cons head₀ tails₀ IHtails =>
    simp at Hpatch
    by_cases HEqx : tails₀.length = x
    . simp [if_pos HEqx] at Hpatch
      rw [← Hpatch, ← HEqx]; simp
    . simp [if_neg HEqx] at Hpatch
      generalize HEq : setr x a tails₀ = tailRes
      cases tailRes with
      | none => simp [HEq] at Hpatch
      | some tails₁ =>
        simp [HEq] at Hpatch; simp [← Hpatch]
        rw [← (length_patch _ _ _ _ HEq), if_neg HEqx]
        apply IHtails; apply HEq

theorem patch_binds_ne :
  ∀ {α : Type} x y (a b : α) l₀ l₁,
    patch x a l₀ l₁ →
    x ≠ y →
    binds y b l₁ →
    binds y b l₀ :=
  by
  intros _ x y a b l₀ l₁ Hpatch HNe Hbinds
  induction l₀ generalizing l₁ with
  | nil => nomatch Hpatch
  | cons head₀ tails₀ IHtails =>
    simp at Hpatch
    by_cases HEqx : tails₀.length = x
    . simp [if_pos HEqx] at Hpatch
      cases l₁ with
      | nil => nomatch Hpatch
      | cons head₁ tails₁ =>
        simp at Hpatch
        rw [← Hpatch.right] at Hbinds
        simp; rw [HEqx, if_neg HNe]
        simp at Hbinds; rw [HEqx, if_neg HNe] at Hbinds
        apply Hbinds
    . simp [if_neg HEqx] at Hpatch
      generalize HEq : setr x a tails₀ = tailRes
      cases tailRes with
      | none => simp [HEq] at Hpatch
      | some tails₀ =>
        simp [HEq] at Hpatch
        cases l₁ with
        | nil => nomatch Hpatch
        | cons head₁ tails₁ =>
          simp at Hpatch
          rw [← Hpatch.right, ← Hpatch.left] at Hbinds
          simp; simp at Hbinds
          rw [length_patch _ _ _ _ HEq]
          by_cases HEqy : tails₀.length = y
          . rw [if_pos HEqy]
            rw [if_pos HEqy] at Hbinds
            apply Hbinds
          . rw [if_neg HEqy]
            rw [if_neg HEqy] at Hbinds
            apply IHtails; apply HEq; apply Hbinds

abbrev TEnv :=
  List (Ty × Stage)

abbrev SEnv :=
  List Ty

@[simp]
def escape : TEnv → TEnv
  | [] => []
  | (τ, .stat) :: tails => (τ, .stat) :: escape tails
  | (τ, .dyn) :: tails => (τ, .stat) :: escape tails

theorem nil_escape : [] = escape [] := by simp

theorem length_escape : ∀ Γ, Γ.length = (escape Γ).length :=
  by
  intro Γ
  induction Γ with
  | nil => simp
  | cons head _ IH =>
    have ⟨τ, 𝕊⟩ := head
    cases 𝕊 <;> (simp; apply IH)

theorem binds_escape : ∀ Γ x τ 𝕊, binds x (τ, 𝕊) Γ → binds x (τ, .stat) (escape Γ) :=
  by
  intros Γ x τ 𝕊
  induction Γ with
  | nil => simp
  | cons head tails IH =>
    have ⟨τ, 𝕊⟩ := head
    cases 𝕊
    all_goals
      simp
      rw [← length_escape]
      by_cases HEq : tails.length = x
      . repeat rw [if_pos HEq]; simp
        intros; assumption
      . repeat rw [if_neg HEq]
        apply IH
