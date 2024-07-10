SRCS=$(shell find src -name "*.idr")

all: build/exec/newt build/exec/newt.js

build/exec/newt: ${SRCS}
	idris2 --build newt.ipkg

build/exec/newt.js: ${SRCS}
	idris2 --cg node -o newt.js -p contrib -c src/Main.idr

test: build/exec/newt
	build/exec/newt newt/*.newt
