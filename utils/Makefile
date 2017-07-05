all: gen-random-po gen-targetted-asserts gen-targetted-clauses po-test

gen-random-po: gen-random-po.cpp
	g++ -std=c++11 gen-random-po.cpp -o gen-random-po

gen-targetted-asserts: gen-targetted-asserts.cpp
	g++ -std=c++11 gen-targetted-asserts.cpp -o gen-targetted-asserts

gen-targetted-clauses: gen-targetted-clauses.cpp
	g++ -std=c++11 gen-targetted-clauses.cpp -o gen-targetted-clauses


po-test: po-test.cpp
	g++ -std=c++11 po-test.cpp -o po-test
    
.PHONY: clean

clean:
	rm -rf gen-random-po po-test gen-targetted-clauses gen-targetted-asserts
