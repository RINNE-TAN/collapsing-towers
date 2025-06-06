
inductive Effects : Type where
  | pure
  | reflect

@[simp]
def union : Effects → Effects → Effects
  | .pure, .pure => .pure
  | .reflect, _ => .reflect
  | _, .reflect => .reflect

@[simp]
instance : EmptyCollection Effects where emptyCollection := .pure

@[simp]
instance : Union Effects where union := union

theorem union_empty : forall φ : Effects, φ ∪ ∅ = φ := by
  intro φ
  cases φ <;> rfl
