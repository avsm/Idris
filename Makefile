DB = --user
PREFIX = $(HOME)

package:
	runhaskell Setup.lhs configure $(DB) --ghc --prefix=$(PREFIX)
	runhaskell Setup.lhs build

install: .PHONY
	runhaskell Setup.lhs install $(DB)

clean:
	runhaskell Setup.lhs clean

.PHONY:
