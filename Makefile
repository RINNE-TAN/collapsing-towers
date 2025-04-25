SRCS = $(shell find CollapsingTowers -type f -name "*.lean")
fmt:
	@for file in $(SRCS); do \
	  if git status --short $$file | grep -q .; then \
	    echo "Format: $$file:"; \
		sed -i 's/^import/-- import/' $$file; \
		sed -i 's/\blemma\b/theorem/g' $$file; \
		lean --run script/Reformat.lean $$file | sponge $$file; \
		sed -i 's/^-- import/import/' $$file; \
		sed -i 's/[[:space:]]\+$$//' $$file; \
		sed -i -e :a -e '/^\n*$$/{$$d;N;};/\n$$/ba' $$file; \
	  else \
		echo "Skip:   $$file:"; \
	  fi; \
	done