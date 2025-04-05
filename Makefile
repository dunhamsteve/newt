OSRCS=$(shell find orig -name "*.idr")
SRCS=$(shell find src -name "*.newt")

# Node shaves off 40% of the time.
# RUNJS=bun run
RUNJS=node

.PHONY:

# all: build/exec/newt build/exec/newt.js build/exec/newt.min.js newt.js
all: newt.js

# Original idris version

build/exec/newt: ${OSRCS}
	idris2 --build newt.ipkg

build/exec/newt.js: ${OSRCS}
	-rm build/*
	idris2 --cg node -o newt.js -p contrib -c orig/Main.idr

build/exec/newt.min.js: ${OSRCS}
	idris2 --cg node -o newt.min.js -p contrib -c orig/Main.idr --directive minimal

orig_aoctest: build/exec/newt
	scripts/orig_aoc

orig_test: build/exec/newt
	scripts/orig_test

# New version

newt.js: ${SRCS}
	$(RUNJS) bootstrap/newt.js src/Main.newt -o newt.js

newt2.js: newt.js
	-rm build/*
	$(RUNJS) newt.js src/Main.newt -o newt2.js

newt3.js: newt2.js
	rm -f build/*
	time $(RUNJS) newt2.js src/Main.newt -o newt3.js
	cmp newt2.js newt3.js

test: newt.js
	scripts/test

aoctest: newt.js
	scripts/aoc

# Misc

vscode:
	cd newt-vscode && vsce package && code --install-extension *.vsix

playground: .PHONY
	cd playground && ./build
