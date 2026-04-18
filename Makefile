SRCS=$(shell find src -name "*.newt")

.PHONY:

all: build/newt.js

newt2: build/newt2.js

newt3: build/newt3.js

test: build/newt.js
	scripts/test

cheztest: build/newt.so
	make test NEWT='chez --program build/newt.so' RUNOUT="chez --script" OUTFILE=tmp/out.ss

aoctest: build/newt.js
	scripts/aoc
	scripts/aoc25

lsp: newt-vscode-lsp/dist/lsp.js playground/src/newt.js

# build / install new LSP vscode extension
vscode-lsp vscode: lsp
	cd newt-vscode-lsp && vsce package && code --install-extension *.vsix

playground: .PHONY
	cd playground && ./build

# prettify newt2 (the version built by latest newt) and run a profile on it
profile: .PHONY build/newt.js build/newt2.js
	rm -f isolate*
	prettier -w build/newt2.js --ignore-path junk.js
	node --prof build/newt2.js -o build/newt3.js src/Main.newt
	node --prof-process isolate* > build/profile.txt
	rm -f isolate*

clean:
	rm  build/*

audit: .PHONY
	(cd playground && npm audit)
	(cd newt-vscode && npm audit)
	(cd newt-vscode-lsp && npm audit)

##

build:
	mkdir -p build

src/Revision.newt: .PHONY build
	sh ./scripts/mkrevision

build/newt.js: ${SRCS} src/Revision.newt
	node bootstrap/newt.js src/Main.newt -o build/newt.js

build/newt2.js: build/newt.js
	node build/newt.js src/Main.newt -o build/newt2.js

build/newt3.js: build/newt2.js
	time node build/newt2.js src/Main.newt -o build/newt3.js
	cmp build/newt2.js build/newt3.js

build/newt.ss: build/newt.js
	node build/newt.js src/Main.newt -o build/newt.ss

build/newt.so: build/newt.ss prim.ss
	chez --script scripts/compile-chez.ss

build/newt2.ss: build/newt.so
	time chez --program build/newt.so src/Main.newt -o build/newt2.ss

build/lsp.js: ${SRCS} build/newt.js
	node build/newt.js src/LSP.newt -o build/lsp.js

newt-vscode-lsp/src/newt.js: build/lsp.js
	cp build/lsp.js $@

playground/src/newt.js: build/lsp.js
	cp build/lsp.js $@

newt-vscode-lsp/dist/lsp.js: newt-vscode-lsp/src/lsp.ts newt-vscode-lsp/src/newt.js
	(cd newt-vscode-lsp && node esbuild.js)
	chmod +x $@


