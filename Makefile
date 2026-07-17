.PHONY: artifact clean

ARTIFACT_NAME := artifact

artifact:
	rm -rf .artifact-tmp $(ARTIFACT_NAME).zip
	mkdir -p .artifact-tmp/$(ARTIFACT_NAME)
	cp -r Instar/ Instar.lean Main.lean \
		lakefile.toml lake-manifest.json lean-toolchain \
		.artifact-tmp/$(ARTIFACT_NAME)/
	cd .artifact-tmp && zip -r ../$(ARTIFACT_NAME).zip $(ARTIFACT_NAME)/ -x "*.md"
	rm -rf .artifact-tmp

clean:
	rm -f $(ARTIFACT_NAME).zip
