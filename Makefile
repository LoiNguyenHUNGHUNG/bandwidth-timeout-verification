.PHONY: all clean

all: Makefile.rocq
	$(MAKE) -f Makefile.rocq

Makefile.rocq: _RocqProject
	rocq makefile -f _RocqProject -o Makefile.rocq

clean:
	@if [ -f Makefile.rocq ]; then $(MAKE) -f Makefile.rocq clean; fi
	$(RM) Makefile.rocq Makefile.rocq.conf
