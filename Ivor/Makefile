GHC = ghc
GHCI = ghci
CXX = g++
CC = gcc
HSLINK = -L/usr/lib/ghc-6.0.1 -lHSrts -lHShaskell98 -lHSlang -lHSlang_cbits -lHSbase -lHSbase_cbits -lHSrts -lHSutil -lm -lgmp
CXXFLAGS = -g -Wall -I/usr/lib/ghc-6.0.1/include
CFLAGS = -g -Wall -I/usr/lib/ghc-6.0.1/include
PACKAGES = -package util
LIBTARGET = libttcore.a
TARGET = tt
PROF =
OPTS = ${PROF} -auto-all -fglasgow-exts ${PACKAGES}

OBJS = Parser.o Nobby.o TTCore.o Gadgets.o State.o Typecheck.o \
       Main.o Datatype.o ICompile.o Grouper.o SC.o Bytecode.o \
       CodegenC.o Tactics.o Display.o Unify.o MakeData.o TT.o

SRCS = Parser.hs Nobby.lhs TTCore.lhs Gadgets.lhs State.lhs \
       Typecheck.lhs Datatype.lhs ICompile.lhs \
       Grouper.lhs SC.lhs Bytecode.lhs CodegenC.lhs Tactics.lhs \
       Display.lhs Unify.lhs MakeData.lhs TT.lhs

all: ${TARGET} 

${TARGET}: 
	${GHC} --make ${OPTS} Main.lhs -o ${TARGET}
#	${GHC} ${OPTS} ${OBJS} -o ${TARGET}

logic: LogicDemo.lhs ${SRCS}
	${GHC} --make ${OPTS} LogicDemo.lhs -o logic

Parser.hs: Parser.y
	happy -g -a -c Parser.y -iParser.out -o Parser.hs.in
	sed 's/error \"reading EOF!\"/TokenEOF/' Parser.hs.in > Parser.hs
	rm Parser.hs.in

ghci: Parser.hs
	${GHCI} ${OPTS} -fglasgow-exts Main.lhs

depend : Parser.hs
	${GHC} -M ${OPTS} ${SRCS}

doc : TT.lhs
	ghc -cpp -E -optP-P -D__HADDOCK__ TT.lhs -o TT.hs
	haddock -h TT.hs -o docs
	rm TT.hs

clean:
	rm -f *.o *.hi Parser.hs Parser.out ${TARGET}

decruft:
	rm -f *~

# Implicit rules for haskell source

%.o: %.lhs
	${GHC} -c ${OPTS} $< -o $@

%.o: %.hs
	${GHC} -c ${OPTS} $< -o $@

%.hi: %.o
	@:

# DO NOT DELETE: Beginning of Haskell dependencies
Gadgets.o : Gadgets.lhs
TT.o : TT.lhs
TT.o : Gadgets.hi
Nobby.o : Nobby.lhs
Nobby.o : Gadgets.hi
Nobby.o : TT.hi
Typecheck.o : Typecheck.lhs
Typecheck.o : Nobby.hi
Typecheck.o : Gadgets.hi
Typecheck.o : TT.hi
Datatype.o : Datatype.lhs
Datatype.o : Nobby.hi
Datatype.o : Typecheck.hi
Datatype.o : Gadgets.hi
Datatype.o : TT.hi
MakeData.o : MakeData.lhs
MakeData.o : Datatype.hi
MakeData.o : TT.hi
ICompile.o : ICompile.lhs
ICompile.o : Gadgets.hi
ICompile.o : Nobby.hi
ICompile.o : Datatype.hi
ICompile.o : TT.hi
Grouper.o : Grouper.lhs
Grouper.o : Nobby.hi
Grouper.o : TT.hi
SC.o : SC.lhs
SC.o : ICompile.hi
SC.o : Nobby.hi
SC.o : TT.hi
SC.o : Grouper.hi
Bytecode.o : Bytecode.lhs
Bytecode.o : TT.hi
Bytecode.o : SC.hi
CodegenC.o : CodegenC.lhs
CodegenC.o : SC.hi
CodegenC.o : Bytecode.hi
Unify.o : Unify.lhs
Unify.o : Typecheck.hi
Unify.o : TT.hi
Unify.o : Nobby.hi
Tactics.o : Tactics.lhs
Tactics.o : Unify.hi
Tactics.o : Gadgets.hi
Tactics.o : Nobby.hi
Tactics.o : Typecheck.hi
Tactics.o : TT.hi
Display.o : Display.lhs
Display.o : Nobby.hi
Display.o : Typecheck.hi
Display.o : TT.hi
Display.o : Tactics.hi
Parser.o : Parser.hs
Parser.o : Datatype.hi
Parser.o : Gadgets.hi
Parser.o : TT.hi
State.o : State.lhs
State.o : Unify.hi
State.o : Display.hi
State.o : Tactics.hi
State.o : CodegenC.hi
State.o : Bytecode.hi
State.o : SC.hi
State.o : Grouper.hi
State.o : ICompile.hi
State.o : MakeData.hi
State.o : Datatype.hi
State.o : Typecheck.hi
State.o : Gadgets.hi
State.o : Nobby.hi
State.o : TT.hi
State.o : Parser.hi
Main.o : Main.lhs
Main.o : State.hi
Main.o : Parser.hi
Main.o : Typecheck.hi
Main.o : Nobby.hi
Main.o : Gadgets.hi
Main.o : TT.hi
HumeTT.o : HumeTT.lhs
HumeTT.o : Tactics.hi
HumeTT.o : Bytecode.hi
HumeTT.o : SC.hi
HumeTT.o : Nobby.hi
HumeTT.o : Gadgets.hi
HumeTT.o : Typecheck.hi
HumeTT.o : State.hi
HumeTT.o : Parser.hi
HumeTT.o : TT.hi
# DO NOT DELETE: End of Haskell dependencies
