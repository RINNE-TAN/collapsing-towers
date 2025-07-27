import CollapsingTowers.TwoLvLBasic.Syntax.Defs
import CollapsingTowers.TwoLvLBasic.Utils.List

abbrev TEnv :=
  List (Ty × Stage)

@[simp]
def escape : TEnv → TEnv
  | [] => []
  | (τ, .stat) :: tails => (τ, .stat) :: escape tails
  | (τ, .dyn) :: tails => (τ, .stat) :: escape tails

lemma escape.nil : [] = escape [] := by simp

lemma escape.length : ∀ Γ, Γ.length = (escape Γ).length :=
  by
  intro Γ
  induction Γ with
  | nil => simp
  | cons head _ IH =>
    have ⟨τ, 𝕊⟩ := head
    cases 𝕊 <;> (simp; apply IH)

lemma binds.escape : ∀ Γ x τ 𝕊, binds x (τ, 𝕊) Γ → binds x (τ, .stat) (escape Γ) :=
  by
  intros Γ x τ 𝕊
  induction Γ with
  | nil => simp
  | cons head tails IH =>
    have ⟨τ, 𝕊⟩ := head
    cases 𝕊
    all_goals
      simp
      rw [← escape.length]
      by_cases HEq : tails.length = x
      . repeat rw [if_pos HEq]; simp
        intros; assumption
      . repeat rw [if_neg HEq]
        apply IH
