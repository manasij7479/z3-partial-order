#include <iostream>
#include <cstdlib>
#include <ctime>
#include <set>
#include <string>

int main(int argc, char **argv) {
  if (argc < 4) {
  	std::cerr << "./gen-random-po num_vars num_positive_atoms num_negative_atoms\n";
  	return 1; 
  }
  int num_vars = std::stoi(argv[1]);
  int num_positive_atoms = std::stoi(argv[2]);
  int num_negative_atoms = std::stoi(argv[3]);

  std::cout << "(declare-sort HB)\n";
  for (int i = 0; i < num_vars; ++i) {
  	std::cout << "(declare-fun v" << i << " () HB)\n";
  }

  std::set<std::pair<int, int>> used;
  
  std::srand(std::time(0));

  for (int i = 0; i < num_positive_atoms; ++i) {
  	int a = std::rand() % num_vars;
  	int b = std::rand() % num_vars;
  	if (a != b && used.find(std::make_pair(a, b)) == used.end()) {
      std::cout << "(assert (partial-order v" << a << " v" << b << "))\n";
      used.insert(std::make_pair(a, b));
  	} else {
      --i;
  	}
  }

  for (int i = 0; i < num_negative_atoms; ++i) {
  	int a = std::rand() % num_vars;
  	int b = std::rand() % num_vars;
  	if (a != b && used.find(std::make_pair(a, b)) == used.end()) {
      std::cout << "(assert (not (partial-order v" << a << " v" << b << ")))\n";
      used.insert(std::make_pair(a, b));
  	} else {
      --i;
  	}
  }

  std::cout << "(assert (distinct";
  for (int i = 0; i < num_vars; ++i) {
  	std::cout << " v" << i;
  }
  std::cout << "))\n(check-sat)\n";
  
  return 0;
}