import CollapsingTowers.TwoLevelMut.SyntacticTyping.Ty
import CollapsingTowers.TwoLevelMut.Utils.Defs

abbrev TEnv :=
  List (Ty × Stage)

notation:max "⦰" => ([] : TEnv)

@[simp]
def erase_env : TEnv → TEnv
  | ⦰ => ⦰
  | (τ, _) :: Γ => (erase_ty τ, 𝟚) :: erase_env Γ
