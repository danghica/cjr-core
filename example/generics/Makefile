REPO := ../..
PYTHON ?= python3
.PHONY: build extract test verify docs benchmark report readable
build extract test verify docs benchmark report readable:
	cd $(REPO) && $(PYTHON) scripts/project.py $@ --example generics
