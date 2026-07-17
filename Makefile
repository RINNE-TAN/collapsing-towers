.PHONY: artifact clean

ARTIFACT_NAME := artifact

artifact:
	rm -f $(ARTIFACT_NAME).zip
	zip -r $(ARTIFACT_NAME).zip \
		Instar/ Instar.lean Main.lean \
		lakefile.toml lake-manifest.json lean-toolchain \
		-x "*.md"

clean:
	rm -f $(ARTIFACT_NAME).zip
