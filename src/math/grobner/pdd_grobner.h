/*++
  Copyright (c) 2017 Microsoft Corporation

  Module Name:

  <name>

  Abstract:

  <abstract>

  Author:
  Nikolaj Bjorner (nbjorner)
  Lev Nachmanson (levnach)

  Revision History:


  --*/
#pragma once

#include "util/dependency.h"
#include "util/obj_hashtable.h"
#include "util/region.h"
#include "util/rlimit.h"
#include "util/statistics.h"
#include "math/dd/dd_pdd.h"

namespace dd {

class grobner {
public:
    struct stats {
        unsigned m_simplified;
        double   m_max_expr_size;
        unsigned m_max_expr_degree;
        unsigned m_superposed;
        unsigned m_compute_steps;
        void reset() { memset(this, 0, sizeof(*this)); }
    };

    struct config {
        unsigned m_eqs_threshold;
        unsigned m_expr_size_limit;
    };

private:
    class equation {
        bool                       m_processed;  //!< state
        unsigned                   m_idx;        //!< position at m_equations
        pdd                        m_poly;       //!< polynomial in pdd form
        u_dependency *             m_dep;        //!< justification for the equality
    public:
        equation(pdd const& p, u_dependency* d, unsigned idx): 
            m_processed(false),
            m_idx(idx),
            m_poly(p),
            m_dep(d)
        {}

        const pdd& poly() const { return m_poly; }        
        u_dependency * dep() const { return m_dep; }
        unsigned hash() const { return m_idx; }
        unsigned idx() const { return m_idx; }
        void operator=(pdd& p) { m_poly = p; }
        void operator=(u_dependency* d) { m_dep = d; }
        bool is_processed() const { return m_processed; }
        void set_processed(bool p) { m_processed = p; }
    };

    typedef obj_hashtable<equation> equation_set;
    typedef ptr_vector<equation> equation_vector;
    typedef std::function<void (u_dependency* d, std::ostream& out)> print_dep_t;

    pdd_manager&                                 m;
    reslimit&                                    m_limit;
    stats                                        m_stats;
    config                                       m_config;
    print_dep_t                                  m_print_dep;
    equation_vector                              m_equations;
    equation_set                                 m_processed;
    equation_set                                 m_to_simplify;
    mutable u_dependency_manager                 m_dep_manager;
    equation_set                                 m_all_eqs;
    bool                                         m_conflict;
public:
    grobner(reslimit& lim, pdd_manager& m);
    ~grobner();

    void operator=(print_dep_t& pd) { m_print_dep = pd; }
    void operator=(config const& c) { m_config = c; }

    void reset();
    void add(pdd const&, u_dependency * dep);

    void compute_basis();

    equation_set const& equations();
    u_dependency_manager& dep() const { return m_dep_manager;  }

    void collect_statistics(statistics & st) const;
    std::ostream& display_equation(std::ostream& out, const equation& eq) const;
    std::ostream& display(std::ostream& out) const;

private:
    bool compute_basis_step();
    equation* pick_next();
    bool canceled();
    bool done();
    void superpose(equation const& eq1, equation const& eq2);
    void superpose(equation const& eq);
    bool simplify_source_target(equation const& source, equation& target, bool& changed_leading_term);
    bool simplify_using(equation_set& set, equation const& eq);
    bool simplify_using(equation& eq, equation_set const& eqs);
    void toggle_processed(equation& eq);

    bool eliminate(equation& eq) { return is_trivial(eq) && (del_equation(&eq), true); }
    bool is_trivial(equation const& eq) const { return eq.poly().is_zero(); }    
    bool is_simpler(equation const& eq1, equation const& eq2) { return eq1.poly() < eq2.poly(); }
    bool check_conflict(equation const& eq) { return eq.poly().is_val() && !is_trivial(eq) && (set_conflict(), true); }    
    void set_conflict() { m_conflict = true; }
    bool is_too_complex(const equation& eq) const { return is_too_complex(eq.poly()); }
    bool is_too_complex(const pdd& p) const { return p.tree_size() > m_config.m_expr_size_limit;  }


    void del_equations(unsigned old_size);
    void del_equation(equation* eq);    

    void invariant() const;

    void update_stats_max_degree_and_size(const equation& e);
};

}
