all: gen-random-po gen-targetted po-test

gen-random-po: gen-random-po.cpp
	g++ -std=c++11 gen-random-po.cpp -o gen-random-po

gen-targetted: gen-targetted.cpp
	g++ -std=c++11 gen-targetted.cpp -o gen-targetted

po-test: po-test.cpp
	g++ -std=c++11 po-test.cpp -o po-test
    
.PHONY: clean

clean:
	rm -rf gen-random-po po-test
