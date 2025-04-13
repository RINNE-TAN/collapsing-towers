SRCS = $(wildcard CollapsingTowers/*.lean)
fmt:
	@for file in $(SRCS); do \
		echo "Processing $$file:"; \
		lean --run script/Reformat.lean $$file | sponge $$file; \
	done