CC=gcc
CFLAGS= -Wall -Wextra -DNDEBUG -O3 #-ggdb3

all: libpicosat.a

clean:
	rm -f *.o *.a *~

picosat.o: picosat.c picosat.h Makefile
	$(CC) $(CFLAGS) -c $<

version.o: version.c config.h Makefile
	$(CC) $(CFLAGS) -c $<

libpicosat.a: picosat.o version.o
	ar rc $@ picosat.o version.o
	ranlib $@

.PHONY: all clean
