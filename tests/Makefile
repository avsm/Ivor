all:
	rm -f tests
	ghc --make -package ivor -package HUnit Test.lhs -o tests
	./tests

clean:
	rm -f *.o *.hi tests

decruft:
	rm -f *~
