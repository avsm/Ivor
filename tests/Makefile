all:
	rm -f tests Test.hi Test.o
	ghc --make -package ivor -package HUnit Test.lhs -o tests
	./tests

clean:
	rm -f *.o *.hi tests

decruft:
	rm -f *~
