import CollapsingTowers.TwoLevelRec.SyntacticTyping.Ty
import CollapsingTowers.TwoLevelRec.Utils.Defs

abbrev TEnv :=
  List (Ty × Stage)

notation:max "⦰" => ([] : TEnv)

@[simp]
def erase_env : TEnv → TEnv
  | [] => []
  | (τ, _) :: Γ => (erase_ty τ, 𝟙) :: erase_env Γ

lemma erase_env.length : ∀ Γ, Γ.length = (erase_env Γ).length :=
  by
  intros Γ
  induction Γ
  case nil => rfl
  case cons IH => simp; apply IH

lemma erase_env.binds : ∀ x τ 𝕊 Γ, binds x (τ, 𝕊) Γ → binds x (erase_ty τ, 𝟙) (erase_env Γ) :=
  by
  intros x τ 𝕊 Γ Hbinds
  induction Γ
  case nil => nomatch Hbinds
  case cons tails IH =>
    by_cases HEq : tails.length = x
    . simp [if_pos HEq] at Hbinds
      simp [← erase_env.length, if_pos HEq, Hbinds]
    . simp [if_neg HEq] at Hbinds
      simp [← erase_env.length, if_neg HEq]
      apply IH; apply Hbinds
