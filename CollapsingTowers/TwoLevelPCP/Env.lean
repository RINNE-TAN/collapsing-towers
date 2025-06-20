
import Mathlib.Data.Nat.Basic
import CollapsingTowers.TwoLevelPCP.Syntax
@[simp]
def indexr {X : Type} (n : ℕ) (l : List X) : Option X :=
  match l with
  | [] => none
  | head :: tails => if tails.length == n then some head else indexr n tails

theorem indexr_iff_lt : ∀ {A} {xs : List A} {i},
  i < xs.length ↔ ∃ x, indexr i xs = some x := by
  intro A xs i;
  constructor
  . intro h; induction xs
    case nil => simp at h
    case cons x xs ih =>
      simp; by_cases h': xs.length = i
      . simp [h']
      . simp [if_neg h']; apply ih; simp at h; omega
  . intro h; induction xs
    case nil => simp at h
    case cons x xs ih =>
      simp at h; by_cases h': xs.length = i
      . subst h'; simp
      . simp [if_neg h'] at h; simp;
        have h' := ih h; omega

abbrev TEnv :=
  List (Ty × Stage)

abbrev SEnv :=
  List Ty

@[simp]
def binds {A : Type} (x : ℕ) (a : A) (Γ : List A) :=
  indexr x Γ = some a

theorem binds_extend : ∀ {A : Type} Γ Δ x (a : A), binds x a Γ → binds x a (Δ ++ Γ) :=
  by
  intros _ Γ Δ x a Hbinds
  induction Δ with
  | nil => apply Hbinds
  | cons head tails IHtails =>
    simp
    by_cases Hx : tails.length + Γ.length = x
    . have Hx : x < Γ.length := by apply indexr_iff_lt.mpr; exists a
      omega
    . rw [if_neg Hx]; apply IHtails

theorem binds_extendr : ∀ {A : Type} Γ Δ x (a : A), binds x a Γ → binds (x + Δ.length) a (Γ ++ Δ) :=
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

theorem binds_shrink : ∀ {A : Type} Γ Δ x (a : A), x < Γ.length → binds x a (Δ ++ Γ) → binds x a Γ :=
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

theorem binds_shrinkr : ∀ {A : Type} Γ Δ x (a : A), binds (x + Δ.length) a (Γ ++ Δ) → binds x a Γ :=
  by
  intros _ Γ Δ x a
  induction Γ with
  | nil =>
    simp; intro Hindexr
    have : x + Δ.length < Δ.length := by apply indexr_iff_lt.mpr; exists a
    omega
  | cons head tails IHtails =>
    simp
    by_cases HEq : tails.length = x
    . repeat rw [if_pos HEq]; simp
    . repeat rw [if_neg HEq]
      apply IHtails

@[simp]
def escape : TEnv → TEnv
  | [] => []
  | (τ, .stat) :: tails => (τ, .stat) :: escape tails
  | (τ, .dyn) :: tails => (τ, .stat) :: escape tails

theorem nil_escape : [] = escape [] := by simp

theorem length_escape : ∀ Γ, Γ.length = (escape Γ).length := by
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
