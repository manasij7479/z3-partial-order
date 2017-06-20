#include <iostream>
#include <cstdlib>
#include <ctime>
#include <set>
#include <string>
#include <fstream>
#include <cassert>

int main(int argc, char **argv) {
  if (argc < 5) {
  	std::cerr << "./gen-random-po num_vars num_positive_atoms num_negative_atoms outfile testfile?\n";
  	return 1; 
  }
  int num_vars = std::stoi(argv[1]);
  int num_positive_atoms = std::stoi(argv[2]);
  int num_negative_atoms = std::stoi(argv[3]);
  std::string outfile = argv[4];

  std::string testfile = argc >5 ? std::string(argv[5]) : std::string("/dev/null");

  std::ofstream out(outfile);
  
  std::ofstream test(testfile);
  
  assert(out.good() && test.good());

  out << "(declare-sort HB)\n";
  for (int i = 0; i < num_vars; ++i) {
  	out << "(declare-fun v" << i << " () HB)\n";
  }
  
  test << num_vars << ' ' << num_positive_atoms << ' ' << num_negative_atoms << '\n';

  std::set<std::pair<int, int>> used;
  
  std::srand(std::time(0));

  for (int i = 0; i < num_positive_atoms; ++i) {
  	int a = std::rand() % num_vars;
  	int b = std::rand() % num_vars;
  	if (a != b && used.find(std::make_pair(a, b)) == used.end()) {
      out << "(assert (partial-order v" << a << " v" << b << "))\n";
      used.insert(std::make_pair(a, b));
      test << a << ' ' << b << '\n';
  	} else {
      --i;
  	}
  }

  for (int i = 0; i < num_negative_atoms; ++i) {
  	int a = std::rand() % num_vars;
  	int b = std::rand() % num_vars;
  	if (a != b && used.find(std::make_pair(a, b)) == used.end()) {
      out << "(assert (not (partial-order v" << a << " v" << b << ")))\n";
      used.insert(std::make_pair(a, b));
      test << a << ' ' << b << '\n';
  	} else {
      --i;
  	}
  }

  out << "(assert (distinct";
  for (int i = 0; i < num_vars; ++i) {
  	out << " v" << i;
  }
  out << "))\n(check-sat)\n";
  
  return 0;
}