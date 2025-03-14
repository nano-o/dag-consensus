JAR=tla2tools.jar
JAR_URL=https://github.com/tlaplus/tlaplus/releases/download/v1.8.0/$(JAR)
TLC_WORKERS=8
TLC_OFFHEAP_MEMORY=20G
TLC_HEAP=5G
TLC_CMD=java -Xmx${TLC_HEAP} -XX:+UseParallelGC -XX:MaxDirectMemorySize=${TLC_OFFHEAP_MEMORY} -Dtlc2.tool.fp.FPSet.impl=tlc2.tool.fp.OffHeapDiskFPSet -Dtlc2.tool.ModelChecker.BAQueue=true -jar tla2tools.jar -workers ${TLC_WORKERS} -checkpoint 30 -deadlock -noGenerateSpecTE
TLA_SPEC?=

# Download the JAR if it does not exist
$(JAR):
	wget -O $@ $(JAR_URL)

# Don't redownload
.PRECIOUS: $(JAR)

%.pdf: %.tla $(JAR)
	java -cp tla2tools.jar tla2tex.TLA -ps -latexCommand pdflatex $<

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

.PHONY: pcal run-tlc
