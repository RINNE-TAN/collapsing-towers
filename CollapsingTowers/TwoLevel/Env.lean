
import Mathlib.Data.Nat.Basic
@[simp]
def indexr {X : Type} (n : ℕ) (l : List X) : Option X :=
  match l with
  | [] => none
  | head :: tails => if n == tails.length then some head else indexr n tails
