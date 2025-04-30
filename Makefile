SRCS = $(shell find CollapsingTowers -type f -name "*.lean")
fmt:
	@for file in $(SRCS); do \
	  if git status --short $$file | grep -q .; then \
		cp $$file $$file.tmp; \
		sed -i 's/^import/-- import/'  $$file.tmp; \
		sed -i 's/\blemma\b/theorem/g'  $$file.tmp; \
		lean --run script/Reformat.lean  $$file.tmp | sponge  $$file.tmp; \
		sed -i 's/^-- import/import/'  $$file.tmp; \
		sed -i 's/[[:space:]]\+$$//'  $$file.tmp; \
		sed -i -e :a -e '/^\n*$$/{$$d;N;};/\n$$/ba'  $$file.tmp; \
		if diff -q $$file.tmp $$file > /dev/null; then \
			echo "Skip:   $$file:"; \
			rm $$file.tmp; \
	  	else \
			echo "Format: $$file:"; \
			mv $$file.tmp $$file; \
	  	fi; \
	  else \
		echo "Skip:   $$file:"; \
	  fi; \
	done

fmt-all:
	@for file in $(SRCS); do \
		cp $$file $$file.tmp; \
		sed -i 's/^import/-- import/'  $$file.tmp; \
		sed -i 's/\blemma\b/theorem/g'  $$file.tmp; \
		lean --run script/Reformat.lean  $$file.tmp | sponge  $$file.tmp; \
		sed -i 's/^-- import/import/'  $$file.tmp; \
		sed -i 's/[[:space:]]\+$$//'  $$file.tmp; \
		sed -i -e :a -e '/^\n*$$/{$$d;N;};/\n$$/ba'  $$file.tmp; \
		if diff -q $$file.tmp $$file > /dev/null; then \
			echo "Skip:   $$file:"; \
			rm $$file.tmp; \
	  	else \
			echo "Format: $$file:"; \
			mv $$file.tmp $$file; \
	  	fi; \
	done