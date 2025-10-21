import Mathlib.Data.Set.Insert

lemma Set.union_diff_union_cancel_left {s t u : Set α} : (s ∪ t) \ (s ∪ u) ≤ t \ u :=
  by
  rw [Set.union_diff_distrib]
  rw [Set.diff_eq_empty.mpr (by simp)]
  rw [Set.empty_union]
  apply Set.diff_subset_diff
  . simp
  . simp

lemma Set.union_diff_union_cancel_right {s t u : Set α} : (t ∪ s) \ (u ∪ s) ≤ t \ u :=
  by
  rw [Set.union_comm t s, Set.union_comm u s]
  apply union_diff_union_cancel_left
