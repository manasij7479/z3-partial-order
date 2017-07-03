all: gen-random-po po-test

gen-random-po: gen-targetted.cpp
	g++ -std=c++11 gen-random-po.cpp -o gen-random-po

po-test: po-test.cpp
	g++ -std=c++11 po-test.cpp -o po-test
    
.PHONY: clean

clean:
	rm -rf gen-random-po po-test
