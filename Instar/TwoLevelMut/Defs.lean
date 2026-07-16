import Instar.TwoLevelMut.Utils.Defs
import Instar.TwoLevelMut.Syntax.Defs
import Instar.TwoLevelMut.OperationalSemantics.Defs
import Instar.TwoLevelMut.SyntacticTyping.Defs
import Instar.TwoLevelMut.SyntacticSoundness.Defs
import Instar.TwoLevelMut.CtxEquiv.Defs
import Instar.TwoLevelMut.LogicalEquiv.Defs
import Instar.TwoLevelMut.SemanticsPreservation.Defs

#check deterministic.decomposition_ctxℙ
#check deterministic

#check progress.strengthened
#check progress
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
