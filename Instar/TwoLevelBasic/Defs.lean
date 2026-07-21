import Instar.TwoLevelBasic.Utils.Defs
import Instar.TwoLevelBasic.Syntax.Defs
import Instar.TwoLevelBasic.OperationalSemantics.Defs
import Instar.TwoLevelBasic.SyntacticTyping.Defs
import Instar.TwoLevelBasic.SyntacticSoundness.Defs
import Instar.TwoLevelBasic.CtxEquiv.Defs
import Instar.TwoLevelBasic.LogicalEquiv.Defs
import Instar.TwoLevelBasic.SemanticsPreservation.Defs

#check deterministic.decomposition_ctxℙ
#check deterministic

#check progress.strengthened
#check progress
#check preservation.open_subst
#check preservation
#check preservation.stepn
#check soundness

#check typing.erase.safety

#check ctx_equiv.trans
#check log_equiv.fundamental
#check log_equiv.soundness

#check semantics_preservation.lets
#check semantics_preservation.reflect.head
#check semantics_preservation
#check semantics_preservation.stepn
#check semantics_preservation.stepn.rep
