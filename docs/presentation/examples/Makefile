.PHONY: all clean gauss gauss_bench

GAUSS_SRC=gauss/gauss.cpp gauss/main.cpp gauss/gauss_pp.cpp gauss/gauss_np.cpp gauss/gauss_fp.cpp
GAUSS_LIB=-lgmpxx -lgmp

gauss: gauss.out
	./gauss.out

gauss.out: $(GAUSS_SRC)
	g++ -o $@ $^ $(GAUSS_LIB) -std=c++17 -Wall -Werror -Wpedantic -O3

sgauss.out: $(GAUSS_SRC)
	g++ -o $@ $^ $(GAUSS_LIB) -std=c++17 -Wall -Werror -Wpedantic -O3 -static -static-libgcc -static-libstdc++

gauss_bench: sgauss.out
	for i in `seq 1 3 200`; do ./sgauss.out "$$i" 42 "res_$$i.csv" "diff_$$i.csv" ; done
	awk '(NR == 1) || (FNR > 1)' diff_*.csv > diff.csv
	awk '(NR == 1) || (FNR > 1)' res_*.csv > res.csv
	rm -rf diff_*.csv res_*.csv

clean:
	rm -rf *.aux *.log *.nav *.out *.snm *.toc *.vrb *.csv
