OBJECTS = $(patsubst %.sig, %.v, $(wildcard *.sig))

all: $(OBJECTS)

%.v: %.sig
	stack exec -- as2-exe -i $^ -o test/$@

