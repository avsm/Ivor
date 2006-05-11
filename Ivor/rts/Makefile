TARGET = testdrive
CC = gcc
CFLAGS = -O

OBJS = closure.o testdrive.o

all: ${TARGET} 

${TARGET}: ${OBJS}
	${CC} ${CFLAGS} ${OBJS} -o ${TARGET} -lgc

clean:
	rm -f ${TARGET} *.o *~

closure.o: closure.h
testdrive.o: closure.h test.c

