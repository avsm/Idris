DB = --user
PREFIX = $(HOME)

PROFILE = 
# -p --enable-executable-profiling

all: .PHONY
	echo "module Idris.Prefix where prefix = \"$(PREFIX)\"" > Idris/Prefix.hs
	runhaskell Setup.lhs configure $(DB) --ghc --prefix=$(PREFIX) $(PROFILE)
	runhaskell Setup.lhs build

install: .PHONY
	runhaskell Setup.lhs install $(DB)
	mkdir -p $(PREFIX)/lib/idris
	install lib/*.idr lib/*.e $(PREFIX)/lib/idris

package: all install

cabal-package:
	runhaskell Setup.lhs sdist

test: .PHONY
	make -C tests
	make -C web/tutorial clean
	make -C web/tutorial

clean:
	runhaskell Setup.lhs clean

.PHONY:
