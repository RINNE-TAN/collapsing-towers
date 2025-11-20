basic:
	lake build CollapsingTowers.TwoLevelBasic.Defs

rec:
	lake build CollapsingTowers.TwoLevelRec.Defs

mut:
	lake build CollapsingTowers.TwoLevelMut.Defs

final:
	lake build CollapsingTowers.TwoLevelFinal.Defs

all: basic rec mut final
