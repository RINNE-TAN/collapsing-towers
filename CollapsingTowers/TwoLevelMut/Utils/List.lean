import Mathlib.Data.Nat.Basic

@[simp]
def getr {α : Type} (x : ℕ) (l : List α) : Option α :=
  match l with
  | [] => none
  | head :: tails => if tails.length == x then some head else getr x tails

lemma getr_exists_iff_index_lt_length : ∀ {α : Type} (l : List α) i, i < l.length ↔ ∃ a, getr i l = some a :=
  by
  intro _ l i; constructor
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

@[simp]
def setr {α : Type} (x : ℕ) (a : α) (l : List α) : Option (List α) :=
  match l with
  | [] => none
  | head :: tails =>
    if tails.length == x then some (a :: tails)
    else do
      let tails ← setr x a tails
      (head :: tails)

lemma setr_exists_iff_index_lt_length : ∀ {α : Type} (l₀ : List α) i a, i < l₀.length ↔ ∃ l₁, setr i a l₀ = some l₁ :=
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

lemma binds.extend : ∀ {α : Type} Γ Δ x (a : α), binds x a Γ → binds x a (Δ ++ Γ) :=
  by
  intros _ Γ Δ x a Hbinds
  induction Δ with
  | nil => apply Hbinds
  | cons head tails IHtails =>
    simp
    by_cases Hx : tails.length + Γ.length = x
    . have Hx : x < Γ.length := by rw [getr_exists_iff_index_lt_length]; exists a
      omega
    . rw [if_neg Hx]; apply IHtails

lemma binds.extendr : ∀ {α : Type} Γ Δ x (a : α), binds x a Γ → binds (x + Δ.length) a (Γ ++ Δ) :=
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

lemma binds.shrink : ∀ {α : Type} Γ Δ x (a : α), x < Γ.length → binds x a (Δ ++ Γ) → binds x a Γ :=
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

lemma binds.shrinkr : ∀ {α : Type} Γ Δ x (a : α), binds (x + Δ.length) a (Γ ++ Δ) → binds x a Γ :=
  by
  intros _ Γ Δ x a
  induction Γ with
  | nil =>
    simp; intro Hgetr
    have : x + Δ.length < Δ.length := by rw [getr_exists_iff_index_lt_length]; exists a
    omega
  | cons head tails IHtails =>
    simp
    by_cases HEq : tails.length = x
    . repeat rw [if_pos HEq]; simp
    . repeat rw [if_neg HEq]
      apply IHtails

@[simp]
def patch {α : Type} (x : ℕ) (a : α) (l₀ : List α) (l₁ : List α) :=
  setr x a l₀ = some l₁

lemma patch.length :
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

lemma patch.binds_eq :
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
        rw [← (patch.length _ _ _ _ HEq), if_neg HEqx]
        apply IHtails; apply HEq

lemma patch.binds_disjoint :
  ∀ {α : Type} x y (a b : α) l₀ l₁,
    patch x a l₀ l₁ →
    x ≠ y →
    binds y b l₀ →
    binds y b l₁ :=
  by
  intros _ x y a b l₀ l₁ Hpatch HNe Hbinds
  induction l₀ generalizing l₁ with
  | nil => nomatch Hpatch
  | cons head₀ tails₀ IHtails =>
    simp at Hpatch
    by_cases HEqx : tails₀.length = x
    . simp [if_pos HEqx] at Hpatch
      simp [HEqx, if_neg HNe] at Hbinds
      cases l₁ with
      | nil => nomatch Hpatch
      | cons head₁ tails₁ =>
        simp at Hpatch
        simp [← Hpatch, HEqx, if_neg HNe]
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
          rw [← Hpatch]
          by_cases HEqy : tails₀.length = y
          . simp [if_pos HEqy]
            simp [patch.length _ _ _ _ HEq, if_pos HEqy] at Hbinds
            apply Hbinds
          . simp [if_neg HEqy]
            apply IHtails; apply HEq
            simp [patch.length _ _ _ _ HEq, if_neg HEqy] at Hbinds
            apply Hbinds
