WASI_SDK ?= $(abspath ../../../wasi-sdk-25.0-x86_64-linux)
CC      := $(WASI_SDK)/bin/wasm32-wasi-clang

SRCS := $(wildcard *.c)
BINS := $(basename $(SRCS))

O0_DIR := O0
O3_DIR := O3

O0_WASMS := $(addprefix $(O0_DIR)/,$(addsuffix .wasm,$(BINS)))
O3_WASMS := $(addprefix $(O3_DIR)/,$(addsuffix .wasm,$(BINS)))

.PHONY: all clean

all: $(O0_WASMS) $(O3_WASMS)

$(O0_DIR)/%.wasm: %.c | $(O0_DIR)
	$(CC) -O0 -o $@ $<

$(O3_DIR)/%.wasm: %.c | $(O3_DIR)
	$(CC) -O3 -o $@ $<

$(O0_DIR) $(O3_DIR):
	mkdir -p $@

clean:
	rm -rf $(O0_DIR) $(O3_DIR)
