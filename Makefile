SRCS=$(shell find src -name "*.newt")

# Node shaves off 40% of the time.
# RUNJS=bun run
RUNJS=node

.PHONY:

all: newt.js


REV=$(shell git rev-parse --short HEAD)
src/Revision.newt: .PHONY
	echo "module Revision\nimport Prelude\ngitRevision : String\ngitRevision = \"${REV}\"" > src/Revision.newt.new
	cmp src/Revision.newt.new src/Revision.newt || cp src/Revision.newt.new src/Revision.newt
	rm -f src/Revision.newt.new

newt.js: ${SRCS} src/Revision.newt
	$(RUNJS) bootstrap/newt.js src/Main.newt -o newt.js

newt2.js: newt.js
	$(RUNJS) newt.js src/Main.newt -o newt2.js

newt3.js: newt2.js
	time $(RUNJS) newt2.js src/Main.newt -o newt3.js
	cmp newt2.js newt3.js

min.js: newt3.js scripts/pack
	scripts/pack
	gzip -kf min.js
	ls -l min.js min.js.gz

test: newt.js
	scripts/test

aoctest: newt.js
	scripts/aoc
	scripts/aoc25

# Misc

vscode:
	cd newt-vscode && vsce package && code --install-extension *.vsix

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

lsp.js: ${SRCS}
	node newt.js src/LSP.newt -o lsp.js

newt-vscode-lsp/src/newt.js: lsp.js .PHONY
	echo "import fs from 'fs'\nlet mods = { fs }\nlet require = key => mods[key]\n" > $@
	# HACK
	perl -p -e "s/(const LSP_(?:updateFile|checkFile|hoverInfo))/export \$$1/" lsp.js >> $@

newt-vscode-lsp/dist/lsp.js: newt-vscode-lsp/src/lsp.ts newt-vscode-lsp/src/newt.js
	(cd newt-vscode-lsp && node esbuild.js)

lsp: newt-vscode-lsp/dist/lsp.js

