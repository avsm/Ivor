DB = --user
PREFIX = $(HOME)
GHCOPTS = 

package:
	runhaskell Setup.lhs configure --user --ghc --prefix=$(PREFIX)
	runhaskell Setup.lhs build

install: .PHONY
	runhaskell Setup.lhs install $(DB)

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
