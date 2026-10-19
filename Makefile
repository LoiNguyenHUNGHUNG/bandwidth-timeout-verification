.PHONY: all clean check

all: Makefile.rocq
	$(MAKE) -f Makefile.rocq

Makefile.rocq: _RocqProject
	rocq makefile -f _RocqProject -o Makefile.rocq

clean:
	@if [ -f Makefile.rocq ]; then $(MAKE) -f Makefile.rocq clean; fi
	$(RM) Makefile.rocq Makefile.rocq.conf

# Recheck every compiled proof and its dependencies with the independent kernel
# checker. The project manifest remains the single list of proof modules.
PROOF_MODULES := $(patsubst theories/%.v,BandwidthTimeout.%,$(filter %.v,$(shell cat _RocqProject)))
check: all
	rocq check -silent -Q theories BandwidthTimeout $(PROOF_MODULES)
