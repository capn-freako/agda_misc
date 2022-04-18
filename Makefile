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
LAGDA_FILES := simple_essence.lagda.md
STATIC := $(PAGES_ROOT)/index.md
TARGS := $(BLD_DIR)/$(LAGDA_FILES:.lagda.md=.md)
TAG_FILE := _pushed

.PHONY: all

all: $(TAG_FILE)

$(TAG_FILE): $(TARGS) $(STATIC)
	@echo "DO NOT DELETE ME!" > $@
	@echo "" >> $@
	git add $(BLD_DIR) >> $@
	git commit -am 'Automatic build/push of capn-freako/agda_misc.' >> $@
	git push >> $@

$(BLD_DIR)/%.md: %.lagda.md
	$(AGDA_EXEC) $(AGDA_OPTS) $<
