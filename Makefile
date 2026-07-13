.DEFAULT_GOAL := all

basic:
	lake build Instar.TwoLevelBasic.Defs

rec:
	lake build Instar.TwoLevelRec.Defs

mut:
	lake build Instar.TwoLevelMut.Defs

final:
	lake build Instar.TwoLevelFinal.Defs

all: basic rec mut final

# Artifact evaluation: check for unfinished proofs (should produce no output)
check-axioms:
	grep -rn -E '\b(axiom|sorry|admit)\b' Instar/ --include="*.lean"; test $$? -eq 1 && echo "PASS: No axioms, sorry, or admit found."

# Full verification: build + axiom check
verify: all check-axioms
	@echo ""
	@echo "========================================="
	@echo "  Artifact verification complete."
	@echo "  All proofs checked. Zero axioms found."
	@echo "========================================="
