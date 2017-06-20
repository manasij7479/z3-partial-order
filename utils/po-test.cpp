#include <iostream>
#include <map>
#include <vector>
#include <queue>
#include <set>
#include <fstream>
#include <cassert>

bool is_connected(std::vector<std::vector<int>>& g, int x, int y) {
  std::queue<int> q;
  q.push(x);
  std::set<int> visited;
  while (!q.empty()) {
    int u = q.front();
    q.pop();
    visited.insert(u);

    for (auto v : g[u]) {
      if (v == y) {
        return true;
      }
      if (visited.find(v) == visited.end()) {
        q.push(v);
      }
    }
  }
  return false;
}

int main(int argc, char** argv) {
  if (argc != 2) {
    std::cerr << "./po-test test-file\n";
    return 1;
  }
  int vars, pos, neg;
  std::ifstream in(argv[1]);
  assert(in.good());
  in >> vars >> pos >> neg;
  
  std::vector<std::vector<int>> graph(vars);
  while (pos--) {
    int x, y;
    in >> x >> y;
    if (is_connected(graph, y, x)) {
      std::cout << "unsat\n";
      return 0;
    }
    graph[x].push_back(y);
  }
  while (neg--) {
    int x, y;
    in >> x >> y;
    // TODO : compute pairwise connectivity in advance
    if (is_connected(graph, x, y)) {
      std::cout << "unsat\n";
      return 0;
    } 
  }
  std::cout << "sat" << std::endl;
  return 0;

}