# DB = 
# PREFIX = /usr/local
DB = --user
PREFIX = $(HOME)

# Set this to -p for profiling libraries too
PROFILE =

CABALOPTS = -O 

package:
	echo "module Ivor.Prefix where prefix = \"$(PREFIX)\"" > Ivor/Prefix.hs
	runhaskell Setup.lhs configure $(DB) $(CABALOPTS) --ghc --prefix=$(PREFIX) $(PROFILE)
	runhaskell Setup.lhs build

install: .PHONY
	runhaskell Setup.lhs install $(DB)
	mkdir -p $(PREFIX)/lib/ivor
	install lib/*.tt $(PREFIX)/lib/ivor

unregister:
	runhaskell Setup.lhs unregister $(DB)

doc:
	runhaskell Setup.lhs haddock

test:
	make -C tests

sdist:
	runhaskell Setup.lhs sdist

jones: .PHONY package install
	cd Jones; ghc $(GHCOPTS) Main.lhs -o jones -package ivor

jones_install: jones
	install Jones/jones $(PREFIX)/bin

iovor: .PHONY package install
	cd IOvor; ghc --make $(GHCOPTS) Main.lhs -o iovor -package ivor

iovor_install: iovor
	install IOvor/iovor $(PREFIX)/bin
	install IOvor/iobasics.tt $(PREFIX)/lib/ivor

clean:
	runhaskell Setup.lhs clean
	rm -f Jones/jones *.o *.hi
	rm -f IOvor/iovor *.o *.hi
	make -C tests clean

decruft:
	rm -f *~
	make -C Ivor decruft
	make -C tests decruft

.PHONY:
