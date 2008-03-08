DB = --user
PREFIX = $(HOME)

all: .PHONY
	echo "module Idris.Prefix where prefix = \"$(PREFIX)\"" > Idris/Prefix.hs
	runhaskell Setup.lhs configure $(DB) --ghc --prefix=$(PREFIX)
	runhaskell Setup.lhs build

install: .PHONY
	runhaskell Setup.lhs install $(DB)
	mkdir -p $(PREFIX)/lib/idris
	install lib/*.idr $(PREFIX)/lib/idris

package: all install

clean:
	runhaskell Setup.lhs clean

.PHONY:
