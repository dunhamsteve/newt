SRCS=$(shell find src -name "*.idr")

all: build/exec/newt

build/exec/newt: ${SRCS}
	idris2 --build newt.ipkg

test: build/exec/newt
	build/exec/newt
