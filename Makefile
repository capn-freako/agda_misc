# Gnu makefile for capn-freako's `agda_misc` GitHub repo.
#
# Original author: David Banas <capn.freako@gmail.com>
# Original date: April 1, 2022
#
# Copyright (c) 2022 David Banas; all rights reserved World wide.

PAGES_ROOT := docs
BLD_DIR := $(PAGES_ROOT)/html
AGDA_EXEC := agda
AGDA_OPTS := --html --html-highlight=auto --html-dir=$(BLD_DIR)
PANDOC_EXEC := pandoc
PANDOC_OPTS := -o $(BLD_DIR)/simple_essence.html -s --indented-code-classes=agda --toc --highlight-style=tango -c Agda.css
LAGDA_FILES := simple_essence.lagda.md
TARGS := $(BLD_DIR)/$(LAGDA_FILES:.lagda.md=.html)

.PHONY: all

.PRECIOUS: $(BLD_DIR)/$(LAGDA_FILES:.lagda.md=.md)

all: $(TARGS)

%.html: %.md
	$(PANDOC_EXEC) $(PANDOC_OPTS) $<

$(BLD_DIR)/%.md: %.lagda.md
	$(AGDA_EXEC) $(AGDA_OPTS) $<

debug:
	@echo "Sources: ${LAGDA_FILES}"
	@echo "Targets: ${TARGS}"
