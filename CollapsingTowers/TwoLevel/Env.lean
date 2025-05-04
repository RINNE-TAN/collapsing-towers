
import Mathlib.Data.Nat.Basic

@[simp]
def indexr {X : Type} (n : ℕ) (l : List X) : Option X :=
  match l with
  | [] => none
  | head :: tails => if tails.length == n then some head else indexr n tails

lemma indexrSome : ∀ {A} (xs : List A) i,
  i < xs.length -> ∃ x, indexr i xs = some x := by
  intro A xs i h; induction xs
  case nil => simp at h
  case cons x xs ih =>
    simp; by_cases h': xs.length = i
    . simp [h']
    . simp [if_neg h']; apply ih; simp at h; omega

lemma indexrSome' : ∀ {A} (xs : List A) i,
  (∃ x, indexr i xs = some x) → i < xs.length := by
  intros A xs i h; induction xs
  case nil => simp at h
  case cons x xs ih =>
    simp at h; by_cases h': xs.length = i
    . subst h'; simp
    . simp [if_neg h'] at h; simp;
      have h' := ih h; omega

lemma indexrHead : ∀ {A} (x : A) (xs : List A),
  indexr xs.length (x :: xs) = some x := by intros A x xs; simp

lemma indexrNone : ∀ {A} (xs : List A) i,
  i >= xs.length -> indexr i xs = none := by
  intros A xs i h; induction xs <;> simp
  case cons x xs ih =>
    simp at h; have h' : ¬ xs.length = i := by omega
    rw [if_neg h']; apply ih; omega
