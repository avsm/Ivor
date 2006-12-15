DB = --user
PREFIX = $(HOME)
# Set this to -p for profiling libraries too
PROFILE =

GHCOPTS = 

package:
	echo "module Ivor.Prefix where prefix = \"$(PREFIX)\"" > Ivor/Prefix.hs
	runhaskell Setup.lhs configure --user --ghc --prefix=$(PREFIX) $(PROFILE)
	runhaskell Setup.lhs build

install: .PHONY
	runhaskell Setup.lhs install $(DB)
	mkdir -p $(PREFIX)/lib/ivor
	install lib/* $(PREFIX)/lib/ivor

unregister:
	runhaskell Setup.lhs unregister $(DB)

doc:
	runhaskell Setup.lhs haddock

test:
	make -C tests

jones: .PHONY package install
	cd Jones; ghc $(GHCOPTS) Main.lhs -o jones -package ivor

jones_install: jones
	install Jones/jones $(PREFIX)/bin

clean:
	runhaskell Setup.lhs clean
	rm -f Jones/jones Main.o Main.hi
	make -C tests clean

decruft:
	rm -f *~
	make -C Ivor decruft
	make -C tests decruft

.PHONY:
