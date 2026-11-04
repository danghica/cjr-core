PYTHON ?= python3
.PHONY: build extract test verify docs paper benchmark report readable dependencies
build extract test verify docs paper benchmark report readable dependencies:
	$(PYTHON) scripts/project.py $@ $(ARGS)

.PHONY: readable-plugin
readable-plugin:
	$(PYTHON) -m tools.rocq_readable.plugin.build
