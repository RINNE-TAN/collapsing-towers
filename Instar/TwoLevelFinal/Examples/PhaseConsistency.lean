import Instar.TwoLevelFinal.Examples.Notation

namespace Phasesemantics_preservation

-- stuck example
-- letsc x (* phase 2 *) = eff in
-- x (* phase 1 *)
example : ∀ b τ ε, ¬typing_reification ⦰ (.lets𝕔 b (.bvar 0)) τ ε :=
  by
  intros _ _ _ Hτ
  cases Hτ <;> contradiction

-- cross stage persistence
-- let x (* phase 1 *) = loc 0 in
-- code x (* phase 2 *)
example : ∀ b τ ε, ¬typing_reification ⦰ (.lets b (.code (.bvar 0))) τ ε :=
  by
  intros _ _ _ Hτ
  cases Hτ
  case pure Hτ =>
    generalize HEqε : ⊥ = ε
    rw [HEqε] at Hτ
    cases Hτ; contradiction
  case reify Hτ =>
    cases Hτ; contradiction

end Phasesemantics_preservation
