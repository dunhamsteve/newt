SRCS=$(shell find src -name "*.newt")

# Node shaves off 40% of the time.
# RUNJS=bun run
RUNJS=node

.PHONY:

all: newt.js

newt.js: ${SRCS}
	-rm build/* >/dev/null
	$(RUNJS) bootstrap/newt.js src/Main.newt -o newt.js

newt2.js: newt.js
	-rm build/*
	$(RUNJS) newt.js src/Main.newt -o newt2.js

newt3.js: newt2.js
	-rm build/*
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

# Misc

vscode:
	cd newt-vscode && vsce package && code --install-extension *.vsix

playground: .PHONY
	cd playground && ./build

profile: .PHONY
	rm isolate* build/*; node --prof newt.js -o newt2.js src/Main.newt
	node --prof-process isolate* > profile.txt

