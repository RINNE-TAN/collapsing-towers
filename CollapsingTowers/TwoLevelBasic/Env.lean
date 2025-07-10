
import Mathlib.Data.Nat.Basic
import CollapsingTowers.TwoLevelBasic.Syntax
@[simp]
def getr {α : Type} (x : ℕ) (l : List α) : Option α :=
  match l with
  | [] => none
  | head :: tails => if tails.length == x then some head else getr x tails

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

@[simp]
def binds {α : Type} (x : ℕ) (a : α) (l : List α) :=
  getr x l = some a

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

abbrev TEnv :=
  List (Ty × Stage)

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
