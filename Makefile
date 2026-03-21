SRCS=$(shell find src -name "*.newt")

# Node shaves off 40% of the time.
# RUNJS=bun run
RUNJS=node

.PHONY:

all: newt.js


src/Revision.newt: .PHONY
	sh ./scripts/mkrevision

newt.js: ${SRCS} src/Revision.newt
	$(RUNJS) bootstrap/newt.js src/Main.newt -o newt.js

newt2.js: newt.js
	$(RUNJS) newt.js src/Main.newt -o newt2.js

newt3.js: newt2.js
	time $(RUNJS) newt2.js src/Main.newt -o newt3.js
	cmp newt2.js newt3.js

newt.ss: newt.js
	$(RUNJS) newt.js src/Main.newt -o newt.ss

newt.so: newt.ss prim.ss
	chez --script scripts/compile-chez.ss

newt2.ss: newt.so
	chez --program newt.ss src/Main.newt -o newt2.ss

test: newt.js
	scripts/test

cheztest: newt.so
	make test NEWT='chez --program newt.so' RUNOUT="chez --script" OUTFILE=tmp/out.ss

aoctest: newt.js
	scripts/aoc
	scripts/aoc25

# Misc

# build / install old vscode extension
# vscode:
	# cd newt-vscode && vsce package && code --install-extension *.vsix

# build / install new LSP vscode extension
vscode-lsp vscode: lsp
	cd newt-vscode-lsp && vsce package && code --install-extension *.vsix

playground: .PHONY
	cd playground && ./build

profile: .PHONY
	rm isolate* build/*; node --prof newt.js -o newt2.js src/Main.newt
	node --prof-process isolate* > profile.txt

clean:
	rm newt*.js iife.js min.js min.js.gz

audit: .PHONY
	(cd playground && npm audit)
	(cd newt-vscode && npm audit)
	(cd newt-vscode-lsp && npm audit)

lsp.js: ${SRCS}
	node newt.js src/LSP.newt -o lsp.js

newt-vscode-lsp/src/newt.js: lsp.js
	cp lsp.js $@

playground/src/newt.js: lsp.js
	cp lsp.js $@

newt-vscode-lsp/dist/lsp.js: newt-vscode-lsp/src/lsp.ts newt-vscode-lsp/src/newt.js
	(cd newt-vscode-lsp && node esbuild.js)
	chmod +x $@

lsp: newt-vscode-lsp/dist/lsp.js playground/src/newt.js

