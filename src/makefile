all: genigme solvigme

genigme : enigme.o genigme.o
		g++ enigme.o genigme.o -o genigme

solvigme : enigme.o solvigme.o
		g++ enigme.o solvigme.o -o solvigme

enigme.o: enigme.cpp
		g++ -c enigme.cpp -o enigme.o

genigme.o : genigme.cpp
		g++ -c genigme.cpp -o genigme.o

solvigme.o : solvigme.cpp
		g++ -c solvigme.cpp -o solvigme.o

clean:
		rm -f *.o
