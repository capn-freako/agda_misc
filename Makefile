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
#PANDOC_OPTS := -o $(BLD_DIR)/simple_essence.html -s --indented-code-classes=agda --toc --highlight-style=tango -c Agda.css
PANDOC_OPTS := --indented-code-classes=agda --toc --highlight-style=tango -c Agda.css
LAGDA_FILES := simple_essence.lagda.md
#PANDOC_OUT := $(BLD_DIR)/$(LAGDA_FILES:.lagda.md=_pandoc.md)
PANDOC_OUT := $(BLD_DIR)/$(LAGDA_FILES:.lagda.md=.html)
#PANDOC_IN := $(PANDOC_OUT:_pandoc.md=.md)
STATIC := $(PAGES_ROOT)/index.md
TARGS := $(PANDOC_OUT)
TAG_FILE := _pushed

.PHONY: all

.PRECIOUS: $(BLD_DIR)/$(LAGDA_FILES:.lagda.md=.md)

all: $(TAG_FILE)

$(TAG_FILE): $(TARGS) $(STATIC)
	@echo "DO NOT DELETE ME!" > $@
	@echo "" >> $@
	git commit -am 'Automatic build/push of capn-freako/agda_misc.' >> $@
	git push >> $@

%.html: %.md
	$(PANDOC_EXEC) $(PANDOC_OPTS) -o $@ $<

$(BLD_DIR)/%.md: %.lagda.md
	$(AGDA_EXEC) $(AGDA_OPTS) $<

debug:
	@echo "Sources: ${LAGDA_FILES}"
	@echo "Targets: ${TARGS}"
