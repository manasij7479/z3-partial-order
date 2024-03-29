#include <iostream>
#include <cstdlib>
#include <ctime>
#include <set>
#include <string>
#include <fstream>
#include <cassert>
#include <vector>
#include <tuple>

class Writer {
public:
  Writer(std::string outfile, int vars, int do_int_)
    : out(outfile), num_vars(vars), do_int(do_int_) {
    assert(out.good() && test.good());
    if (do_int == 0) {
      out << "(set-logic QF_IDL)\n";
    }
    if( do_int == 1 || do_int == 2 ) {
      out << "(declare-sort HB)\n";
    }
    // test << vars << ' ' << pos << ' ' << neg << '\n';
  }
  void writeVar(int x) {
    std::string t_name = "HB";
    if( do_int == 0 ) t_name = "Int";
    out << "(declare-fun v" << x << " () " << t_name << ")\n";
  }

  void writePositveAtom(int a, int b) {
    out << "(" << get_ord_name() << " v" << a << " v" << b << ")";
    // test << a << ' ' << b << '\n';
  }

  void writeNegativeAtom(int a, int b) {
    out << "(not ";
    writePositveAtom(a,b);
    out <<")";
    // test << a << ' ' << b << '\n';
  }

  inline std::string get_ord_name() {
    if( do_int == 0 ) return "<";
    if( do_int == 1 ) return "partial-order";
    if( do_int == 2 ) return "linear-order";
    else assert(false);
  }

  void writeClause( std::vector< std::tuple<int,int,bool> > vec ) {
    out << "(or ";
    for( auto tup : vec ) {
      int a = std::get<0>(tup);
      int b = std::get<1>(tup);
      int isPos = std::get<2>(tup);
      if( isPos )
        writePositveAtom(a,b);
      else
        writeNegativeAtom(a,b);
      out << " ";
    }
    out <<")";
  }

  void writeAssertClause( std::vector< std::tuple<int,int,bool> > vec ) {
    out << "(assert ";
    writeClause(vec);
    out <<")\n";
  }

  void writeAssertPositveAtom(int a, int b) {
    out << "(assert ";
    writePositveAtom(a,b);
    out <<")\n";
  }


  void writeAssertNegativeAtom(int a, int b) {
    out << "(assert ";
    writeNegativeAtom(a,b);
    out <<")\n";
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
  int do_int;
};

int main(int argc, char **argv) {
  if (argc < 7) {
  	std::cerr << "./gen-targetted num_vars num_clauses neg_prob clause_size outfile do_int\n";
  	return 1; 
  }
  int num_vars = std::stoi(argv[1]);
  int num_clauses = std::stoi(argv[2]);
  int neg_prob = std::stoi(argv[3]);
  int clause_size = std::stoi(argv[4]);
  std::string outfile = argv[5];
  std::string mode = argv[6];
  int do_int = 0;
  if( mode == "idl" ) {
    do_int = 0;
  }else if( mode == "po" ) {
    do_int = 1;
  }else if( mode == "lo" ) {
    do_int = 2;
  }else{
    std::cerr << "wrong options!!\n";
    return 1;
  }

  // int do_int = argv[5])(argc == 7) ? 1 : 0; 

  Writer writer(outfile, num_vars, do_int);

  // out << "(declare-sort HB)\n";
  for (int i = 0; i < num_vars; ++i) {
  	writer.writeVar(i);
  }

  // std::set<std::pair<int, int>> used;
  
  std::srand(std::time(0));

  std::vector< std::tuple<int,int,bool> > vec;
  int a,b;
  bool isPos;

  for(int i = 0; i < num_clauses; ++i ) {
    for( int j =0; j < clause_size; j++ ) {
      isPos = (std::rand() % 100) >= neg_prob;
      do{
        a = std::rand() % num_vars;
        b = std::rand() % num_vars;
      } while( a == b);
      if (b < a) std::swap(a, b);
      vec.push_back( std::make_tuple(a,b,isPos) );
    }
    writer.writeAssertClause( vec );
    vec.clear();
  }
  
  return 0;
}
