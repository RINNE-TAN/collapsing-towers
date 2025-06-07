
import Mathlib.Data.Nat.Basic
import CollapsingTowers.TwoLevelPCP.Syntax
@[simp]
def indexr {X : Type} (n : ℕ) (l : List X) : Option X :=
  match l with
  | [] => none
  | head :: tails => if tails.length == n then some head else indexr n tails

theorem indexrSome : ∀ {A} (xs : List A) i,
  i < xs.length → ∃ x, indexr i xs = some x := by
  intro A xs i h; induction xs
  case nil => simp at h
  case cons x xs ih =>
    simp; by_cases h': xs.length = i
    . simp [h']
    . simp [if_neg h']; apply ih; simp at h; omega

theorem indexrSome' : ∀ {A} (xs : List A) i,
  (∃ x, indexr i xs = some x) → i < xs.length := by
  intros A xs i h; induction xs
  case nil => simp at h
  case cons x xs ih =>
    simp at h; by_cases h': xs.length = i
    . subst h'; simp
    . simp [if_neg h'] at h; simp;
      have h' := ih h; omega

abbrev TEnv :=
  List (Ty × Stage)

@[simp]
def binds (x : ℕ) (τ : Ty) (𝕊 : Stage) (Γ : TEnv) :=
  indexr x Γ = some (τ, 𝕊)

theorem binds_extend : ∀ Γ Δ x τ 𝕊, binds x τ 𝕊 Γ → binds x τ 𝕊 (Δ ++ Γ) :=
  by
  intros Γ Δ x τ 𝕊 Hbinds
  induction Δ with
  | nil => apply Hbinds
  | cons head tails IHtails =>
    simp
    by_cases Hx : tails.length + Γ.length = x
    . have Hx : x < Γ.length := by apply indexrSome'; exists (τ, 𝕊)
      omega
    . rw [if_neg Hx]; apply IHtails

theorem binds_extendr : ∀ Γ Δ x τ 𝕊, binds x τ 𝕊 Γ → binds (x + Δ.length) τ 𝕊 (Γ ++ Δ) :=
  by
  intros Γ Δ x τ 𝕊
  induction Γ with
  | nil => simp
  | cons head tails IHtails =>
    simp
    by_cases HEq : tails.length = x
    . repeat rw [if_pos HEq]; simp
    . repeat rw [if_neg HEq]
      apply IHtails

theorem binds_shrink : ∀ Γ Δ x τ 𝕊, x < Γ.length → binds x τ 𝕊 (Δ ++ Γ) → binds x τ 𝕊 Γ :=
  by
  intros Γ Δ x τ 𝕊 HLt
  induction Δ with
  | nil => simp
  | cons head tails IHtails =>
    intro Hbinds; apply IHtails
    simp at *
    have HNe : tails.length + Γ.length ≠ x := by omega
    rw [if_neg HNe] at Hbinds
    apply Hbinds

theorem binds_shrinkr : ∀ Γ Δ x τ 𝕊, binds (x + Δ.length) τ 𝕊 (Γ ++ Δ) → binds x τ 𝕊 Γ :=
  by
  intros Γ Δ x τ 𝕊
  induction Γ with
  | nil =>
    simp; intro Hindexr
    have : x + Δ.length < Δ.length := by apply indexrSome'; exists (τ, 𝕊)
    omega
  | cons head tails IHtails =>
    simp
    by_cases HEq : tails.length = x
    . repeat rw [if_pos HEq]; simp
    . repeat rw [if_neg HEq]
      apply IHtails
