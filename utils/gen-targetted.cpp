#include <iostream>
#include <cstdlib>
#include <ctime>
#include <set>
#include <string>
#include <fstream>
#include <cassert>

bool do_int = true;


class Writer {
public:
  Writer(std::string outfile, std::string testfile, int vars, int pos, int neg)
    : out(outfile), test(testfile), num_vars(vars) {
    assert(out.good() && test.good());
    out << "(declare-sort HB)\n";
    test << vars << ' ' << pos << ' ' << neg << '\n';
  }
  void writeVar(int x) {
    std::string t_name = "HB";
    if( do_int ) t_name = "Int";
    out << "(declare-fun v" << x << " () " << t_name << ")\n";
  }
  void writePositveAtom(int a, int b) {
    std::string ord_name = "partial-order";
    if( do_int ) ord_name = "<";
    out << "(assert (" << ord_name << " v" << a << " v" << b << "))\n";
    test << a << ' ' << b << '\n';
  }
  void writeNegativeAtom(int a, int b) {
    std::string ord_name = "partial-order";
    if( do_int ) ord_name = "<";
    out << "(assert (not (" << ord_name << " v" << a << " v" << b << ")))\n";
    test << a << ' ' << b << '\n';
    // FIXME : Need a new syntax for test if positive and negative atoms can be mixed in the test.
  }
  ~Writer() {
    out << "(assert (distinct";
    for (int i = 0; i < num_vars; ++i) {
      out << " v" << i;
    }
    out << "))\n(check-sat)\n";
    out.close();
    test.close();
  }
private:  
  std::ofstream out;
  std::ofstream test;
  int num_vars;
};

int main(int argc, char **argv) {
  if (argc < 5) {
  	std::cerr << "./gen-targetted num_vars num_atoms percent_positive outfile testfile?\n";
  	return 1; 
  }
  int num_vars = std::stoi(argv[1]);
  int num_atoms = std::stoi(argv[2]);
  int percent_positive = std::stoi(argv[3]);
  int num_positive_atoms = num_atoms * percent_positive / 100;
  int num_negative_atoms = num_atoms - num_positive_atoms;
  std::string outfile = argv[4];

  std::string testfile = argc >5 ? std::string(argv[5]) : std::string("/dev/null");

  Writer writer(outfile, testfile, num_vars, num_positive_atoms, num_negative_atoms);

  // out << "(declare-sort HB)\n";
  for (int i = 0; i < num_vars; ++i) {
  	writer.writeVar(i);
  }

  std::set<std::pair<int, int>> used;
  
  std::srand(std::time(0));

  for (int i = 0; i < num_positive_atoms; ++i) {
  	int a = std::rand() % num_vars;
  	int b = std::rand() % num_vars; 

  	if (a != b && used.find(std::make_pair(a, b)) == used.end()) {
      if (b < a) std::swap(a, b);
      writer.writePositveAtom(a, b);
      used.insert(std::make_pair(a, b));
  	} else {
      --i;
  	}
  }

  for (int i = 0; i < num_negative_atoms; ++i) {
  	int a = std::rand() % num_vars;
  	int b = std::rand() % num_vars;
  	if (a != b && used.find(std::make_pair(a, b)) == used.end()) {
      if (b < a) std::swap(a, b);
      writer.writeNegativeAtom(a, b);
      used.insert(std::make_pair(a, b));
  	} else {
      --i;
  	}
  }
  
  return 0;
}
