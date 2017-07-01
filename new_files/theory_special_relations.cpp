/*++
Copyright (c) 2015 Microsoft Corporation

Module Name:

    theory_special_relations.cpp

Abstract:

    Special Relations theory plugin.

Author:

    Nikolaj Bjorner (nbjorner) 2015-9-16

Notes:

--*/

#include "theory_special_relations.h"
#include "smt_context.h"
#include "theory_arith.h"
#include <fstream>

#include <unordered_map>

#include "smt/smt_solver.h"
#include "solver/solver.h"
#include "reg_decl_plugins.h"

namespace smt {

    void theory_special_relations::relation::push() {
        m_scopes.push_back(scope());
        scope& s = m_scopes.back();
        s.m_asserted_atoms_lim = m_asserted_atoms.size();
        s.m_asserted_qhead_old = m_asserted_qhead;
        m_graph.push();
        m_ufctx.get_trail_stack().push_scope();
    }

    void theory_special_relations::relation::pop(unsigned num_scopes) {
        unsigned new_lvl = m_scopes.size() - num_scopes;
        scope& s = m_scopes[new_lvl];
        m_asserted_atoms.shrink(s.m_asserted_atoms_lim);
        m_asserted_qhead = s.m_asserted_qhead_old;
        m_scopes.shrink(new_lvl);
        m_graph.pop(num_scopes);
        m_ufctx.get_trail_stack().pop_scope(num_scopes);
    }

    void theory_special_relations::relation::ensure_var(theory_var v) {
        while ((unsigned)v > m_uf.mk_var());
        if ((unsigned)v >= m_graph.get_num_nodes()) {
            m_graph.init_var(v);
        }
    }

    bool theory_special_relations::relation::new_eq_eh(literal l, theory_var v1, theory_var v2) {
        ensure_var(v1);
        ensure_var(v2);
        literal_vector ls;
        ls.push_back(l);
        return
            m_graph.enable_edge(m_graph.add_edge(v1, v2, s_integer(0), ls)) &&
            m_graph.enable_edge(m_graph.add_edge(v2, v1, s_integer(0), ls));
    }

    theory_special_relations::theory_special_relations(ast_manager& m):
        theory(m.mk_family_id("special_relations")),
        m_util(m), m_autil(m) {
        params_ref params;
        params.set_bool("model", true);
        params.set_bool("unsat_core", true);

//        reg_decl_plugins(m_nested_ast_mgr);
        m_nested_solver = mk_smt_solver(m, params, symbol("QFLIA"));
        m_int_sort = m_autil.mk_int();
    }

    theory_special_relations::~theory_special_relations() {
        reset_eh();
    }

    theory * theory_special_relations::mk_fresh(context * new_ctx) {
        return alloc(theory_special_relations, new_ctx->get_manager());
    }

    bool theory_special_relations::internalize_atom(app * atm, bool gate_ctx) {
        TRACE("special_relations", tout << mk_pp(atm, get_manager()) << "\n";);
        SASSERT(m_util.is_special_relation(atm));
        relation* r = 0;
        if (!m_relations.find(atm->get_decl(), r)) {
          //todo: push pop may get misaligned if the following alloc happens after push
            r = alloc(relation, m_util.get_property(atm), atm->get_decl());
            m_relations.insert(atm->get_decl(), r);
        }
        context& ctx = get_context();
        expr* arg0 = atm->get_arg(0);
        expr* arg1 = atm->get_arg(1);
        theory_var v0 = mk_var(arg0);
        theory_var v1 = mk_var(arg1);
        bool_var v = ctx.mk_bool_var(atm);
        ctx.set_var_theory(v, get_id());
        atom* a = alloc(atom, v, *r, v0, v1);
        m_atoms.push_back(a);
        m_bool_var2atom.insert(v, a);
        return true;
    }

    theory_var theory_special_relations::mk_var(expr* e) {
        context& ctx = get_context();
        if (!ctx.e_internalized(e)) {
            ctx.internalize(e, false);
        }
        enode * n = ctx.get_enode(e);
        theory_var v = n->get_th_var(get_id());
        if (null_theory_var == v) {
            v = theory::mk_var(n);
            ctx.attach_th_var(n, this, v);
        }
        return v;
    }

    void theory_special_relations::new_eq_eh(theory_var v1, theory_var v2) {
        context& ctx = get_context();
        app_ref eq(get_manager());
        app* t1 = get_enode(v1)->get_owner();
        app* t2 = get_enode(v2)->get_owner();
        eq = get_manager().mk_eq(t1, t2);
        VERIFY(internalize_atom(eq, false));
        literal l(ctx.get_literal(eq));
        obj_map<func_decl, relation*>::iterator it = m_relations.begin(), end = m_relations.end();
        for (; !ctx.inconsistent() && it != end; ++it) {
            relation& r = *it->m_value;
            if (!r.new_eq_eh(l, v1, v2)) {
                set_neg_cycle_conflict(r);
                break;
            }
        }
    }

    final_check_status theory_special_relations::final_check_eh() {
        TRACE("special_relations", tout << "\n";);
        obj_map<func_decl, relation*>::iterator it = m_relations.begin(), end = m_relations.end();
        lbool r = l_true;
        for (; it != end && r == l_true; ++it) {
            r = final_check(*it->m_value);
        }
        switch (r) {
        case l_undef:
            return FC_GIVEUP;
        case l_false:
            return FC_CONTINUE;
        default:
            break;
        }
        it = m_relations.begin();
        bool new_equality = false;
        for (; it != end; ++it) {
            if (extract_equalities(*it->m_value)) {
                new_equality = true;
            }
        }
        if (new_equality) {
            return FC_CONTINUE;
        }
        else {
            return FC_DONE;
        }
    }

    lbool theory_special_relations::final_check_lo(relation& r) {
        // all constraints are saturated by propagation.
        return l_true;
    }

    enode* theory_special_relations::ensure_enode(expr* e) {
        context& ctx = get_context();
        if (!ctx.e_internalized(e)) {
            ctx.internalize(e, false);
        }
        enode* n = ctx.get_enode(e);
        ctx.mark_as_relevant(n);
        return n;
    }

    literal theory_special_relations::mk_literal(expr* _e) {
        expr_ref e(_e, get_manager());
        context& ctx = get_context();
        ensure_enode(e);
        return ctx.get_literal(e);
    }

    theory_var theory_special_relations::mk_var(enode* n) {
        if (is_attached_to_var(n)) {
            return n->get_th_var(get_id());
        }
        else {
            theory_var v = theory::mk_var(n);
            get_context().attach_th_var(n, this, v);
            get_context().mark_as_relevant(n);
            return v;
        }
    }

    lbool theory_special_relations::final_check_plo(relation& r) {
        //
        // ensure that !Rxy -> Ryx between connected components
        // (where Rzx & Rzy or Rxz & Ryz for some z)
        //
        lbool res = l_true;
        for (unsigned i = 0; res == l_true && i < r.m_asserted_atoms.size(); ++i) {
            atom& a = *r.m_asserted_atoms[i];
            if (!a.phase() && r.m_uf.find(a.v1()) == r.m_uf.find(a.v2())) {
                res = enable(a);
            }
        }
        return res;
    }

    lbool theory_special_relations::final_check_to(relation& r) {
        uint_set visited, target;
        lbool res = l_true;
        for (unsigned i = 0; res == l_true && i < r.m_asserted_atoms.size(); ++i) {
            atom& a = *r.m_asserted_atoms[i];
            if (!a.phase() && r.m_uf.find(a.v1()) == r.m_uf.find(a.v2())) {
                target.reset();
                theory_var w;
                // v2 !<= v1 is asserted
                target.insert(a.v2());
                if (r.m_graph.reachable(a.v1(), visited, target, w)) {
                    // we already have v1 <= v2
                    continue;
                }
                target.reset();
                if (r.m_graph.reachable(a.v2(), target, visited, w)) {
                    // there is a common successor
                    // v1 <= w
                    // v2 <= w
                    // v1 !<= v2
                    // -> v1 <= w & v2 <= w & v1 !<= v2 -> v2 <= v1
                    unsigned timestamp = r.m_graph.get_timestamp();
                    r.m_explanation.reset();
                    r.m_graph.find_shortest_reachable_path(a.v1(), w, timestamp, r);
                    r.m_graph.find_shortest_reachable_path(a.v2(), w, timestamp, r);
                    r.m_explanation.push_back(a.explanation());
                    literal_vector const& lits = r.m_explanation;
                    if (!r.m_graph.enable_edge(r.m_graph.add_edge(a.v2(), a.v1(), s_integer(0), lits))) {
                        set_neg_cycle_conflict(r);
                        res = l_false;
                    }
                }
                // TODO: check if algorithm correctly produces all constraints.
                // e.g., if we add an edge, do we have to repeat the loop?
                //
            }
        }
        return res;
    }

    lbool theory_special_relations::enable(atom& a) {
        if (!a.enable()) {
            relation& r = a.get_relation();
            set_neg_cycle_conflict(r);
            return l_false;
        }
        else {
            return l_true;
        }
    }

    void theory_special_relations::set_neg_cycle_conflict(relation& r) {
        r.m_explanation.reset();
        r.m_graph.traverse_neg_cycle2(false, r);
        set_conflict(r);
    }

    void theory_special_relations::set_conflict(relation& r) {
        literal_vector const& lits = r.m_explanation;
        context & ctx = get_context();
        vector<parameter> params;
        ctx.set_conflict(
            ctx.mk_justification(
                ext_theory_conflict_justification(
                    get_id(), ctx.get_region(),
                    lits.size(), lits.c_ptr(), 0, 0, params.size(), params.c_ptr())));
    }

    lbool theory_special_relations::final_check(relation& r) {
        lbool res = propagate(r);
        if (res != l_true) return res;
        switch (r.m_property) {
        case sr_lo:
            res = final_check_lo(r);
            break;
        case sr_po:
            res = final_check_po(r);
            break;
        case sr_plo:
            res = final_check_plo(r);
            break;
        case sr_to:
            res = final_check_to(r);
            break;
        default:
            UNREACHABLE();
            res = l_undef;
        }
        return res;
    }

    bool theory_special_relations::extract_equalities(relation& r) {
        bool new_eq = false;
        int_vector scc_id;
        u_map<unsigned> roots;
        context& ctx = get_context();
        r.m_graph.compute_zero_edge_scc(scc_id);
        for (unsigned i = 0, j = 0; i < scc_id.size(); ++i) {
            if (scc_id[i] == -1) {
                continue;
            }
            enode* n = get_enode(i);
            if (roots.find(scc_id[i], j)) {
                enode* m = get_enode(j);
                if (n->get_root() != m->get_root()) {
                    new_eq = true;
                    unsigned timestamp = r.m_graph.get_timestamp();
                    r.m_explanation.reset();
                    r.m_graph.find_shortest_zero_edge_path(i, j, timestamp, r);
                    r.m_graph.find_shortest_zero_edge_path(j, i, timestamp, r);
                    eq_justification js(ctx.mk_justification(theory_axiom_justification(get_id(), ctx.get_region(), r.m_explanation.size(), r.m_explanation.c_ptr())));
                    ctx.assign_eq(n, m, js);
                }
            }
            else {
                roots.insert(scc_id[i], i);
            }
        }
        return new_eq;
    }

    /*
      \brief Propagation for piecewise linear orders
    */
    lbool theory_special_relations::propagate_plo(atom& a) {
        lbool res = l_true;
        relation& r = a.get_relation();
        if (a.phase()) {
            r.m_uf.merge(a.v1(), a.v2());
            res = enable(a);
        }
        else if (r.m_uf.find(a.v1()) == r.m_uf.find(a.v2())) {
            res = enable(a);
        }
        return res;
    }

    lbool theory_special_relations::propagate_po(atom& a) {
//        lbool res = l_true;
//        // if (a.phase()) {
//        //   res = enable(a);
//        // }
//        relation& r = a.get_relation();
//        if (a.phase()) {
//            r.m_uf.merge(a.v1(), a.v2());
//            res = enable(a);
//        }
//        else if (r.m_uf.find(a.v1()) == r.m_uf.find(a.v2())) {
////             res = enable(a);
//        }
//        return res;
        return l_true;
    }

    void populate_k_vars(int v, int k,  std::unordered_map<int, std::vector<func_decl*>>& map, int& curr_id, ast_manager& m, sort** int_sort) {
        auto need = map.find(v) == map.end() ? k : k - map[v].size();
        for (auto i = 0; i < need; ++i) {
            map[v].push_back(m.mk_func_decl(symbol(curr_id++), 0, int_sort, *int_sort));
        }
    }

    lbool theory_special_relations::final_check_po(relation& r) {
//        lbool res = l_true;
//        for (unsigned i = 0; res == l_true && i < r.m_asserted_atoms.size(); ++i) {
//            atom& a = *r.m_asserted_atoms[i];
//            if (a.phase()) {
//                r.m_uf.merge(a.v1(), a.v2());
//                res = enable(a);
//            }
//        }
//        for (unsigned i = 0; res == l_true && i < r.m_asserted_atoms.size(); ++i) {
//            atom& a = *r.m_asserted_atoms[i];
//            if (!a.phase() && r.m_uf.find(a.v1()) == r.m_uf.find(a.v2())) {
//                // v1 !-> v2
//                // find v1 -> v3 -> v4 -> v2 path
//                r.m_explanation.reset();
//                unsigned timestamp = r.m_graph.get_timestamp();
//                if (r.m_graph.find_shortest_reachable_path(a.v1(), a.v2(), timestamp, r)) {
//                    r.m_explanation.push_back(a.explanation());
//                    set_conflict(r);
//                    res = l_false;
//                }
//            }
//        }
//        return res;
        context& ctx = get_context();
        ast_manager& m = ctx.get_manager();

        bool first_iter = true;
        int k = 2;
        int curr_id = 100000000; // TODO : How to 'reserve' IDs and check if one is in use?


        std::vector<expr*> assumptions(r.m_asserted_atoms.size());
        std::vector<expr*> conjunctions(r.m_asserted_atoms.size());
        std::vector<expr*> disjunctions(r.m_asserted_atoms.size());

        std::unordered_map<int, std::vector<func_decl*>> map;

        while (true) {
            std::unordered_map<unsigned, unsigned> assume_atom_map;
            if (first_iter) {
                for (unsigned i = 0; /*res == l_true &&*/ i < r.m_asserted_atoms.size(); ++i) {
                    atom& a = *r.m_asserted_atoms[i];
                    populate_k_vars(a.v1(), k, map, curr_id, m, &m_int_sort);
                    populate_k_vars(a.v2(), k, map, curr_id, m, &m_int_sort);

                    conjunctions[i] = m_autil.mk_le(m.mk_app(map[a.v1()][0], unsigned(0),
                            nullptr), m.mk_app(map[a.v2()][0], unsigned(0), nullptr));

                    disjunctions[i] = m_autil.mk_lt(m.mk_app(map[a.v1()][0], unsigned(0),
                            nullptr), m.mk_app(map[a.v2()][0], unsigned(0), nullptr));


                    for (int j = 1; j < k; ++j) {
                        conjunctions[i] = m.mk_and(conjunctions[i], m_autil.mk_le(m.mk_app(map[a.v1()][j], unsigned(0),
                                        nullptr), m.mk_app(map[a.v2()][j], unsigned(0), nullptr)));
                        disjunctions[i] = m.mk_or(disjunctions[i], m_autil.mk_lt(m.mk_app(map[a.v1()][j], unsigned(0),
                                       nullptr), m.mk_app(map[a.v2()][j], unsigned(0), nullptr)));
                    }

                    auto bool_sort = m.mk_bool_sort();
                    auto b = m.mk_func_decl(symbol(curr_id++), 0, &bool_sort, bool_sort);
                    if (a.phase()) {
                      m_nested_solver->assert_expr(m.mk_implies(m.mk_app(b, unsigned(0), nullptr),
                                                              m.mk_and(conjunctions[i], disjunctions[i])));
                    } else {
                      m_nested_solver->assert_expr(m.mk_implies(m.mk_app(b, unsigned(0), nullptr),
                                                              m.mk_not(m.mk_and(conjunctions[i], disjunctions[i]))));
                    }
                    assumptions[i] = m.mk_app(b, unsigned(0), nullptr);
                    assume_atom_map[assumptions[i]->get_id()] = i;
                }
                first_iter = false;
            } else {
                // TODO : Combine with above loop
                for (unsigned i = 0; /*res == l_true &&*/ i < r.m_asserted_atoms.size(); ++i) {
                    atom& a = *r.m_asserted_atoms[i];
                    populate_k_vars(a.v1(), k, map, curr_id, m, &m_int_sort);
                    populate_k_vars(a.v2(), k, map, curr_id, m, &m_int_sort);

//                    conjunctions[i] = m_autil.mk_le(m.mk_app(map[a.v1()][0], unsigned(0),
//                            nullptr), m.mk_app(map[a.v2()][0], unsigned(0), nullptr));

//                    disjunctions[i] = m_autil.mk_lt(m.mk_app(map[a.v1()][0], unsigned(0),
//                            nullptr), m.mk_app(map[a.v2()][0], unsigned(0), nullptr));


//                    for (int j = 1; j < k; ++j) {
                        conjunctions[i] = m.mk_and(conjunctions[i], m_autil.mk_le(m.mk_app(map[a.v1()][k-1], unsigned(0),
                                        nullptr), m.mk_app(map[a.v2()][k-1], unsigned(0), nullptr)));
                        disjunctions[i] = m.mk_or(disjunctions[i], m_autil.mk_lt(m.mk_app(map[a.v1()][k-1], unsigned(0),
                                       nullptr), m.mk_app(map[a.v2()][k-1], unsigned(0), nullptr)));
//                    }

                    auto bool_sort = m.mk_bool_sort();
                    auto b = m.mk_func_decl(symbol(curr_id++), 0, &bool_sort, bool_sort);
                    if (a.phase()) {
                      m_nested_solver->assert_expr(m.mk_implies(m.mk_app(b, unsigned(0), nullptr),
                                                              m.mk_and(conjunctions[i], disjunctions[i])));
                    } else {
                      m_nested_solver->assert_expr(m.mk_implies(m.mk_app(b, unsigned(0), nullptr),
                                                              m.mk_not(m.mk_and(conjunctions[i], disjunctions[i]))));
                    }
                    assumptions[i] = m.mk_app(b, unsigned(0), nullptr);

                }
            }

            if (m_nested_solver->check_sat(assumptions.size(), assumptions.data()) == l_false) {
              // Unsat Core logic goes here
                expr_ref_vector core(m);
                m_nested_solver->get_unsat_core(core);
                if (true || core.size() <= 1) { // TODO: Check if core has more than one cycle.
                    set_conflict(r);
                    // TODO : Set 'explanation' in r
                    for (expr* e : core) {
                        atom& a = *r.m_asserted_atoms[assume_atom_map[e->get_id()]];


                    }
                    return l_false;
                } else {
                    k++;
                    // How to reset old asserts?
                }

            } else {
                return l_true;
            }
        }
        UNREACHABLE();
        return l_true;
    }

    lbool theory_special_relations::propagate(relation& r) {
        lbool res = l_true;
        while (res == l_true && r.m_asserted_qhead < r.m_asserted_atoms.size()) {
            atom& a = *r.m_asserted_atoms[r.m_asserted_qhead];
            switch (r.m_property) {
            case sr_lo:
                res = enable(a);
                break;
            case sr_plo:
                res = propagate_plo(a);
                break;
            case sr_po:
                res = propagate_po(a);
                break;
            default:
                if (a.phase()) {
                    res = enable(a);
                }
                break;
            }
            ++r.m_asserted_qhead;
        }
        return res;
    }

    void theory_special_relations::reset_eh() {
        obj_map<func_decl, relation*>::iterator it = m_relations.begin(), end = m_relations.end();
        for (; it != end; ++it) {
            dealloc(it->m_value);
        }
        m_relations.reset();
        del_atoms(0);
    }

    void theory_special_relations::assign_eh(bool_var v, bool is_true) {
        TRACE("special_relations", tout << "assign bv" << v << " " << (is_true?" <- true":" <- false") << "\n";);
        atom* a;
        VERIFY(m_bool_var2atom.find(v, a));
        a->set_phase(is_true);
        a->get_relation().m_asserted_atoms.push_back(a);
    }

    void theory_special_relations::push_scope_eh() {
        obj_map<func_decl, relation*>::iterator it = m_relations.begin(), end = m_relations.end();
        for (; it != end; ++it) {
            it->m_value->push();
        }
        m_atoms_lim.push_back(m_atoms.size());
    }

    void theory_special_relations::pop_scope_eh(unsigned num_scopes) {
        obj_map<func_decl, relation*>::iterator it = m_relations.begin(), end = m_relations.end();
        for (; it != end; ++it) {
            it->m_value->pop(num_scopes);
        }
        unsigned new_lvl = m_atoms_lim.size() - num_scopes;
        del_atoms(m_atoms_lim[new_lvl]);
    }

    void theory_special_relations::del_atoms(unsigned old_size) {
        atoms::iterator begin = m_atoms.begin() + old_size;
        atoms::iterator it    = m_atoms.end();
        while (it != begin) {
            --it;
            atom * a     = *it;
            m_bool_var2atom.erase(a->var());
            dealloc(a);
        }
        m_atoms.shrink(old_size);
    }


    void theory_special_relations::collect_statistics(::statistics & st) const {
        obj_map<func_decl, relation*>::iterator it = m_relations.begin(), end = m_relations.end();
        for (; it != end; ++it) {
            it->m_value->m_graph.collect_statistics(st);
        }
    }

    model_value_proc * theory_special_relations::mk_value(enode * n, model_generator & mg) {
        UNREACHABLE();
        return 0;
    }

    void theory_special_relations::ensure_strict(graph& g) {
        unsigned sz = g.get_num_edges();
        for (unsigned i = 0; i < sz; ++i) {
            if (!g.is_enabled(i)) continue;
            if (g.get_weight(i) != s_integer(0)) continue;
            dl_var src = g.get_source(i);
            dl_var dst = g.get_target(i);
            if (get_enode(src)->get_root() == get_enode(dst)->get_root()) continue;
            VERIFY(g.enable_edge(g.add_edge(src, dst, s_integer(-1), literal_vector())));
        }
        TRACE("special_relations", g.display(tout););
    }

    void theory_special_relations::ensure_tree(graph& g) {
        unsigned sz = g.get_num_nodes();
        for (unsigned i = 0; i < sz; ++i) {
            int_vector const& edges = g.get_in_edges(i);
            for (unsigned j = 0; j < edges.size(); ++j) {
                edge_id e1 = edges[j];
                if (g.is_enabled(e1)) {
                    SASSERT (i == g.get_target(e1));
                    dl_var src1 = g.get_source(e1);
                    for (unsigned k = j + 1; k < edges.size(); ++k) {
                        edge_id e2 = edges[k];
                        if (g.is_enabled(e2)) {
                            dl_var src2 = g.get_source(e2);
                            if (get_enode(src1)->get_root() == get_enode(src2)->get_root()) continue;
                            if (!disconnected(g, src1, src2)) continue;
                            VERIFY(g.enable_edge(g.add_edge(src1, src2, s_integer(-1), literal_vector())));
                        }
                    }
                }
            }
        }
        TRACE("special_relations", g.display(tout););
    }

    bool theory_special_relations::disconnected(graph const& g, dl_var u, dl_var v) const {
        s_integer val_u = g.get_assignment(u);
        s_integer val_v = g.get_assignment(v);
        if (val_u == val_v) return u != v;
        if (val_u < val_v) {
            std::swap(u, v);
            std::swap(val_u, val_v);
        }
        SASSERT(val_u > val_v);
        svector<dl_var> todo;
        todo.push_back(u);
        while (!todo.empty()) {
            u = todo.back();
            todo.pop_back();
            if (u == v) {
                return false;
            }
            SASSERT(g.get_assignment(u) <= val_u);
            if (g.get_assignment(u) <= val_v) {
                continue;
            }
            int_vector const& edges = g.get_out_edges(u);
            for (unsigned i = 0; i < edges.size(); ++i) {
                edge_id e = edges[i];
                if (is_strict_neighbour_edge(g, e)) {
                    todo.push_back(g.get_target(e));
                }
            }
        }
        return true;
    }

    expr_ref theory_special_relations::mk_inj(relation& r, model_generator& mg) {
      // context& ctx = get_context();
        ast_manager& m = get_manager();
        r.push();
        ensure_strict(r.m_graph);
        func_decl_ref fn(m);
        expr_ref result(m);
        arith_util arith(m);
        sort* const* ty = r.decl()->get_domain();
        fn = m.mk_fresh_func_decl("inj", 1, ty, arith.mk_int());
        unsigned sz = r.m_graph.get_num_nodes();
        func_interp* fi = alloc(func_interp, m, 1);
        for (unsigned i = 0; i < sz; ++i) {
            s_integer val = r.m_graph.get_assignment(i);
            expr* arg = get_enode(i)->get_owner();
            fi->insert_new_entry(&arg, arith.mk_numeral(val.to_rational(), true));
        }
        TRACE("special_relations", r.m_graph.display(tout););
        r.pop(1);
        fi->set_else(arith.mk_numeral(rational(0), true));
        mg.get_model().register_decl(fn, fi);
        result = arith.mk_le(m.mk_app(fn,m.mk_var(0, *ty)), m.mk_app(fn, m.mk_var(1, *ty)));
        return result;
    }

    expr_ref theory_special_relations::mk_class(relation& r, model_generator& mg) {
      //context& ctx = get_context();
        ast_manager& m = get_manager();
        expr_ref result(m);
        func_decl_ref fn(m);
        arith_util arith(m);
        func_interp* fi = alloc(func_interp, m, 1);
        sort* const* ty = r.decl()->get_domain();
        fn = m.mk_fresh_func_decl("class", 1, ty, arith.mk_int());
        unsigned sz = r.m_graph.get_num_nodes();
        for (unsigned i = 0; i < sz; ++i) {
            unsigned val = r.m_uf.find(i);
            expr* arg = get_enode(i)->get_owner();
            fi->insert_new_entry(&arg, arith.mk_numeral(rational(val), true));
        }
        fi->set_else(arith.mk_numeral(rational(0), true));
        mg.get_model().register_decl(fn, fi);
        result = m.mk_eq(m.mk_app(fn, m.mk_var(0, *ty)), m.mk_app(fn, m.mk_var(1, *ty)));
        return result;
    }

    expr_ref theory_special_relations::mk_interval(relation& r, model_generator& mg, unsigned_vector & lo, unsigned_vector& hi) {
        graph const& g = r.m_graph;
        //context& ctx = get_context();
        ast_manager& m = get_manager();
        expr_ref result(m);
        func_decl_ref lofn(m), hifn(m);
        arith_util arith(m);
        func_interp* lofi = alloc(func_interp, m, 1);
        func_interp* hifi = alloc(func_interp, m, 1);
        sort* const* ty = r.decl()->get_domain();
        lofn = m.mk_fresh_func_decl("lo", 1, ty, arith.mk_int());
        hifn = m.mk_fresh_func_decl("hi", 1, ty, arith.mk_int());
        unsigned sz = g.get_num_nodes();
        for (unsigned i = 0; i < sz; ++i) {
            expr* arg = get_enode(i)->get_owner();
            lofi->insert_new_entry(&arg, arith.mk_numeral(rational(lo[i]), true));
            hifi->insert_new_entry(&arg, arith.mk_numeral(rational(hi[i]), true));
        }
        lofi->set_else(arith.mk_numeral(rational(0), true));
        hifi->set_else(arith.mk_numeral(rational(0), true));
        mg.get_model().register_decl(lofn, lofi);
        mg.get_model().register_decl(hifn, hifi);
        result = m.mk_and(arith.mk_le(m.mk_app(lofn, m.mk_var(0, *ty)), m.mk_app(lofn, m.mk_var(1, *ty))),
                          arith.mk_le(m.mk_app(hifn, m.mk_var(1, *ty)), m.mk_app(hifn, m.mk_var(0, *ty))));
        return result;
    }

    void theory_special_relations::init_model_lo(relation& r, model_generator& m) {
        expr_ref inj = mk_inj(r, m);
        func_interp* fi = alloc(func_interp, get_manager(), 2);
        fi->set_else(inj);
        m.get_model().register_decl(r.decl(), fi);
    }

    void theory_special_relations::init_model_plo(relation& r, model_generator& m) {
        expr_ref inj = mk_inj(r, m);
        expr_ref cls = mk_class(r, m);
        func_interp* fi = alloc(func_interp, get_manager(), 2);
        fi->set_else(get_manager().mk_and(inj, cls));
        m.get_model().register_decl(r.decl(), fi);
    }

    void theory_special_relations::init_model_po(relation& r, model_generator& mg) {
        // NOT_IMPLEMENTED_YET();
    }

    /**
       \brief map each node to an interval of numbers, such that
       the children are proper sub-intervals.
       Then the <= relation becomes interval containment.

       1. For each vertex, count the number of nodes below it in the transitive closure.
          Store the result in num_children.
       2. Identify each root.
       3. Process children, assigning unique (and disjoint) intervals.
       4. Extract interpretation.


     */

    void theory_special_relations::init_model_to(relation& r, model_generator& mg) {
        unsigned_vector num_children, lo, hi;
        graph const& g = r.m_graph;
        r.push();
        ensure_strict(r.m_graph);
        ensure_tree(r.m_graph);
        count_children(g, num_children);
        assign_interval(g, num_children, lo, hi);
        expr_ref iv = mk_interval(r, mg, lo, hi);
        r.pop(1);
        func_interp* fi = alloc(func_interp, get_manager(), 2);
        fi->set_else(iv);
        mg.get_model().register_decl(r.decl(), fi);
    }

    bool theory_special_relations::is_neighbour_edge(graph const& g, edge_id edge) const {
        CTRACE("special_relations_verbose", g.is_enabled(edge),
              tout << edge << ": " << g.get_source(edge) << " " << g.get_target(edge) << " ";
              tout << (g.get_assignment(g.get_source(edge)) - g.get_assignment(g.get_target(edge))) << "\n";);

        return
            g.is_enabled(edge) &&
            g.get_assignment(g.get_source(edge)) - g.get_assignment(g.get_target(edge)) == s_integer(1);
    }

    bool theory_special_relations::is_strict_neighbour_edge(graph const& g, edge_id e) const {
        return is_neighbour_edge(g, e) && g.get_weight(e) != s_integer(0);
    }

    void theory_special_relations::count_children(graph const& g, unsigned_vector& num_children) {
        unsigned sz = g.get_num_nodes();
        svector<dl_var> nodes;
        num_children.resize(sz, 0);
        svector<bool>   processed(sz, false);
        for (unsigned i = 0; i < sz; ++i) nodes.push_back(i);
        while (!nodes.empty()) {
            dl_var v = nodes.back();
            if (processed[v]) {
                nodes.pop_back();
                continue;
            }
            unsigned nc = 1;
            bool all_p = true;
            int_vector const& edges = g.get_out_edges(v);
            for (unsigned i = 0; i < edges.size(); ++i) {
                edge_id e = edges[i];
                if (is_strict_neighbour_edge(g, e)) {
                    dl_var dst = g.get_target(e);
                    TRACE("special_relations", tout << v << " -> " << dst << "\n";);
                    if (!processed[dst]) {
                        all_p = false;
                        nodes.push_back(dst);
                    }
                    nc += num_children[dst];
                }
            }
            if (all_p) {
                nodes.pop_back();
                num_children[v] = nc;
                processed[v] = true;
            }
        }
        TRACE("special_relations",
              for (unsigned i = 0; i < sz; ++i) {
                  tout << i << ": " << num_children[i] << "\n";
              });
    }

    void theory_special_relations::assign_interval(graph const& g, unsigned_vector const& num_children, unsigned_vector& lo, unsigned_vector& hi) {
        svector<dl_var> nodes;
        unsigned sz = g.get_num_nodes();
        lo.resize(sz, 0);
        hi.resize(sz, 0);
        unsigned offset = 0;
        for (unsigned i = 0; i < sz; ++i) {
            bool is_root = true;
            int_vector const& edges = g.get_in_edges(i);
            for (unsigned j = 0; is_root && j < edges.size(); ++j) {
                is_root = !g.is_enabled(edges[j]);
            }
            if (is_root) {
                lo[i] = offset;
                hi[i] = offset + num_children[i] - 1;
                offset = hi[i] + 1;
                nodes.push_back(i);
            }
        }
        while (!nodes.empty()) {
            dl_var v = nodes.back();
            int_vector const& edges = g.get_out_edges(v);
            unsigned l = lo[v];
            unsigned h = hi[v];
            nodes.pop_back();
            for (unsigned i = 0; i < edges.size(); ++i) {
                SASSERT(l <= h);
                if (is_strict_neighbour_edge(g, edges[i])) {
                    dl_var dst = g.get_target(edges[i]);
                    lo[dst] = l;
                    hi[dst] = l + num_children[dst] - 1;
                    l = hi[dst] + 1;
                    nodes.push_back(dst);
                }
            }
            SASSERT(l == h);
        }
    }

    void theory_special_relations::init_model(model_generator & m) {
        obj_map<func_decl, relation*>::iterator it = m_relations.begin(), end = m_relations.end();
        for (; it != end; ++it) {
            switch (it->m_value->m_property) {
            case sr_lo:
                init_model_lo(*it->m_value, m);
                break;
            case sr_plo:
                init_model_plo(*it->m_value, m);
                break;
            case sr_to:
                init_model_to(*it->m_value, m);
                break;
            case sr_po:
                init_model_po(*it->m_value, m);
                break;
            default:
              UNREACHABLE(); //ASHU: added to remove warning! Should be supported!
            }
        }
    }

    void theory_special_relations::display(std::ostream & out) const {
        if (m_relations.empty()) return;
        out << "Theory Special Relations\n";
        display_var2enode(out);
        obj_map<func_decl, relation*>::iterator it = m_relations.begin(), end = m_relations.end();
        for (; it != end; ++it) {
            out << mk_pp(it->m_value->decl(), get_manager()) << ":\n";
            it->m_value->m_graph.display(out);
            it->m_value->m_uf.display(out);
            for (unsigned i = 0; i < it->m_value->m_asserted_atoms.size(); ++i){
              atom& a = *it->m_value->m_asserted_atoms[i];
            display_atom( out, a );
            }
        }
    }

  //BEGIN: ASHU
  void theory_special_relations::collect_asserted_po_atoms( vector< std::pair<bool_var,bool> >& atoms) const {
    obj_map<func_decl, relation*>::iterator it = m_relations.begin(), end = m_relations.end();
    for (; it != end; ++it) {
      relation& r = *(it->m_value );
      if( r.m_property != sr_po ) continue;
      // SASSERT( r.m_asserted_qhead == r.m_asserted_atoms.size() );
      for (unsigned i = 0; i < r.m_asserted_atoms.size(); ++i) {
        atom& a = *r.m_asserted_atoms[i];
        atoms.push_back( std::make_pair(a.var(),a.phase()) );
      }
    }
    // for (unsigned i = 0; i < m_asserted_qhead; i++) {
    //     bound * b = m_asserted_bounds[i];
    //     if (b->is_atom()) {
    //       atom* a = static_cast<atom*>(b);
    //       bool_var bv = a->get_bool_var();
    //       bool istr = a->is_true();
    //       atoms.push_back( std::make_pair(bv,istr) );
    //     }
    // }
  }

void theory_special_relations::display_atom( std::ostream & out, atom& a ) const {
    context& ctx = get_context();
    expr* e = ctx.bool_var2expr( a.var() );
    if( !a.phase() ) out << "(not ";
    out << mk_pp( e, get_manager());
    if( !a.phase() ) out << ")";
     out << "\n";
  }
void theory_special_relations::display_atom( atom& a) const {
  display_atom( std::cerr, a);
}
  //END: ASHU

}
