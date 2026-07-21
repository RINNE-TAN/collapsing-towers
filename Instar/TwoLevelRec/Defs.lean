import Instar.TwoLevelRec.Utils.Defs
import Instar.TwoLevelRec.Syntax.Defs
import Instar.TwoLevelRec.OperationalSemantics.Defs
import Instar.TwoLevelRec.SyntacticTyping.Defs
import Instar.TwoLevelRec.SyntacticSoundness.Defs
import Instar.TwoLevelRec.CtxEquiv.Defs
import Instar.TwoLevelRec.LogicalEquiv.Defs
import Instar.TwoLevelRec.SemanticsPreservation.Defs

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
