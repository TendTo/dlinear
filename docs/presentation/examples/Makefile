.PHONY: all clean

GAUSS_SRC=gauss/gauss.cpp gauss/main.cpp gauss/gauss_pp.cpp gauss/gauss_np.cpp gauss/gauss_fp.cpp
GAUSS_LIB=-lgmpxx -lgmp

gauss: gauss.out
	./gauss.out

gauss.out: $(GAUSS_SRC)
	g++ -o $@ $^ $(GAUSS_LIB) -std=c++17 -Wall -Werror -Wpedantic -O3

static: $(GAUSS_SRC)
	g++ -o $@ $^ $(GAUSS_LIB) -std=c++17 -Wall -Werror -Wpedantic -O3 -static -static-libgcc -static-libstdc++

clean:
	rm -rf *.aux *.log *.nav *.out *.snm *.toc *.vrb