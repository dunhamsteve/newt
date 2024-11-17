SRCS=$(shell find src -name "*.idr")

.PHONY:

all: build/exec/newt build/exec/newt.js
# build/exec/newt.min.js

build/exec/newt: ${SRCS}
	idris2 --build newt.ipkg

build/exec/newt.js: ${SRCS}
	idris2 --cg node -o newt.js -p contrib -c src/Main.idr

build/exec/newt.min.js: ${SRCS}
	idris2 --cg node -o newt.min.js -p contrib -c src/Main.idr --directive minimal

test: build/exec/newt
	scripts/test

vscode:
	cd newt-vscode && vsce package && code --install-extension *.vsix

playground: .PHONY
	cd playground && ./build
