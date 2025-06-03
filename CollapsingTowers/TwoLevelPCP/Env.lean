
import Mathlib.Data.Nat.Basic
import CollapsingTowers.TwoLevelPCP.Syntax
@[simp]
def indexr {X : Type} (n : ℕ) (l : List X) : Option X :=
  match l with
  | [] => none
  | head :: tails => if tails.length == n then some head else indexr n tails

abbrev TEnv :=
  List (Ty × Stage)

@[simp]
def binds (x : ℕ) (τ : Ty) (𝕊 : Stage) (Γ : TEnv) :=
  indexr x Γ = some (τ, 𝕊)
