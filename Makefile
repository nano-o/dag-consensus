JAR=tla2tools.jar
JAR_URL=https://github.com/tlaplus/tlaplus/releases/download/v1.8.0/$(JAR)
TLC_WORKERS=8
TLC_OFFHEAP_MEMORY=12G
TLC_HEAP=4G
TLA_SPEC?=
TLC_CFG ?= $(abspath $(basename $(TLA_SPEC))).cfg
TLC_CMD=java -Xmx${TLC_HEAP} -XX:+UseParallelGC -XX:MaxDirectMemorySize=${TLC_OFFHEAP_MEMORY} \
	-Dtlc2.tool.fp.FPSet.impl=tlc2.tool.fp.OffHeapDiskFPSet \
	-Dtlc2.tool.ModelChecker.BAQueue=true \
	-jar $(abspath $(JAR)) \
	-workers ${TLC_WORKERS} \
	-checkpoint 30 \
	-deadlock \
	-noGenerateSpecTE \
	-config '$(TLC_CFG)'

# Download the JAR if it does not exist
$(JAR):
	wget -O $@ $(JAR_URL)

# Don't redownload
.PRECIOUS: $(JAR)

sany: $(JAR) $(TLA_SPEC)
	@if [ -z "$(TLA_SPEC)" ]; then \
	  echo "Error: TLA_SPEC is not set. Use make sany TLA_SPEC=YourSpec.tla"; \
	  exit 1; \
	fi
	java -cp $(JAR) tla2sany.SANY $(TLA_SPEC)

%.pdf: %.tla $(JAR)
	java -cp tla2tools.jar tla2tex.TLA -ps -latexCommand pdflatex $<
	@latexmk -c -quiet -e '$$clean_ext .= " synctex.gz fdb_latexmk dvi ps tex";' $(basename $<).tex

trans: $(JAR) $(TLA_SPEC)
	@if [ -z "$(TLA_SPEC)" ]; then \
	  echo "Error: TLA_SPEC is not set. Use make run-tlc TLA_SPEC=YourSpec.tla"; \
	  exit 1; \
	fi
	java -cp $(JAR) pcal.trans -nocfg $(TLA_SPEC)


run-tlc: $(JAR) $(TLA_SPEC)
	@if [ -z "$(TLA_SPEC)" ]; then \
	  echo "Error: TLA_SPEC is not set. Use make run-tlc TLA_SPEC=YourSpec.tla"; \
	  exit 1; \
	fi
	$(TLC_CMD) $(TLA_SPEC)

# prevents TLC from filling your disk:
run-tlc-diskcap: $(JAR) $(TLA_SPEC)
	@if [ -z "$(TLA_SPEC)" ]; then \
	  echo "Error: TLA_SPEC is not set. Use make run-tlc-diskcap TLA_SPEC=YourSpec.tla"; \
	  exit 1; \
	fi
	TLC_CMD='$(TLC_CMD)' \
	TLC_WORK_IMG='$(HOME)/.cache/tlc/.tlc-work.img' \
	TLC_WORK_MOUNT='$(XDG_RUNTIME_DIR)/tlc-work' \
	./scripts/run_tlc_diskcap.sh '$(abspath $(TLA_SPEC))'

block-dag-test: TLA_SPEC=BlockDagTest.tla
block-dag-test: $(JAR)
	$(TLC_CMD) $(TLA_SPEC)

.PHONY: sany trans run-tlc block-dag-test run-tlc-diskcap
