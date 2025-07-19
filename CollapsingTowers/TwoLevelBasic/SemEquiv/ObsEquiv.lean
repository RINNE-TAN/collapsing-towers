
import CollapsingTowers.TwoLevelBasic.SemEquiv.Fundamental
inductive ObsCtx : Ctx → Prop where
  | hole : ObsCtx id
