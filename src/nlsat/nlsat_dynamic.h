#pragma once

#include "nlsat/nlsat_types.h"
#include "nlsat/nlsat_clause.h"
#include "nlsat/nlsat_assignment.h"
#include "util/hashtable.h"
#include "nlsat/nlsat_solver.h"
/**
 * @brief Dynamic Manager for nlsat
 */

#define DTRACE(CODE) TRACE("dnlsat", CODE)
#define DCTRACE(COND, CODE) CTRACE("dnlsat", COND, CODE)

namespace nlsat {
    // dynamic mode:
    // hybrid - 1
    #define UNIFORM_MODE 1
    // bool_first - 2
    #define BOOL_FIRST_MODE 2
    // theory_first - 3
    #define THEORY_FIRST_MODE 3
    // static bool first - 4
    #define ORIGIN_STATIC_BOOL_FIRST_MODE 4

    // define search mode
    // #define DYNAMIC_MODE BOOL_FIRST_MODE
    #define DYNAMIC_MODE THEORY_FIRST_MODE
    // #define DYNAMIC_MODE UNIFORM_MODE
    // #define DYNAMIC_MODE ORIGIN_STATIC_BOOL_FIRST_MODE


    enum search_mode {
        BOOL, ARITH, INIT, FINISH, SWITCH
    };

    using stage = var;
    using literal_index = var;
    using atom_index = var;
    using clause_index = var;
    using hybrid_var = var;
    using hybrid_var_vector = var_vector;

    // hastable for var
    struct var_hash {
        unsigned operator()(var x) const {
            return x;
        }
    };

    struct var_eq {
        bool operator()(var x, var y) const {
            return x == y;
        }
    };

    using var_table = hashtable<var, var_hash, var_eq>;
    using bool_var_table = var_table;
    using hybrid_var_table = var_table;
    using hybrid_var_pair = std::pair<var, var>;
    using var_vector_vector = vector<var_vector>;
    using var_table_vector = vector<var_table>;

    class dynamic_atom {
    private:
        atom_index m_index;
        atom const * m_atom;
    public:
        var_table m_vars;
        dynamic_atom(atom_index id, atom const * at, var_table const & vars): 
        m_index(id), m_atom(at), m_vars(vars) {}
        ~dynamic_atom(){}

        unsigned get_index() const {
            return m_index;
        }

        atom const * get_atom() const {
            return m_atom;
        }
    };

    class dynamic_clause {
    private:
        clause_index m_index;
        clause const * m_clause;
    public:
        hybrid_var_pair m_watched_var;
        var_table m_vars;
        bool_var_table m_bool_vars;
        dynamic_clause(clause_index id, clause const * cls, var_table const & vars, var_table const & bool_vars): 
        m_index(id), m_clause(cls), m_vars(vars), m_bool_vars(bool_vars) {
            m_watched_var = hybrid_var_pair(null_var, null_var);
        }
        ~dynamic_clause(){}

        unsigned get_index() const {
            return m_index;
        }

        clause const * get_clause() const {
            return m_clause;
        }

        void set_watched_var(hybrid_var x, hybrid_var y) {
            m_watched_var.first = x;
            m_watched_var.second = y;
        }

        var get_another_watched_var(hybrid_var x) const {
            SASSERT(m_watched_var.first == x || m_watched_var.second == x);
            return m_watched_var.first - x + m_watched_var.second;
        }
    };

    using dynamic_atom_vector = vector<dynamic_atom *>;
    using dynamic_clause_vector = vector<dynamic_clause *>;

    class Dynamic_manager {
    public:
        struct imp;
    private:
        imp * m_imp;
    public:
        Dynamic_manager(anum_manager & am, pmanager & pm, assignment & ass, svector<lbool> const & bvalues, bool_var_vector const & pure_bool_vars, bool_var_vector const & pure_bool_convert, solver & s, clause_vector const & clauses, clause_vector & learned, 
        atom_vector const & atoms, unsigned & restart, unsigned & deleted);
        ~Dynamic_manager();

        // set num of arit vars
        void set_var_num(unsigned x);
        // initialize
        void init_search();

        void init_learnt_management();
        void update_learnt_management();
        void init_nof_conflicts();
        void minimize_learned();

        void reset_curr_conflicts();
        void inc_curr_conflicts();
        void reset_curr_literal_assign();
        void inc_curr_literal_assign();
        bool check_restart_requirement();

        hybrid_var get_last_assigned_hybrid_var(bool & is_bool) const;
        var get_last_assigned_arith_var() const;
        unsigned assigned_size() const;
        unsigned assigned_arith_size() const;
        unsigned assigned_bool_size() const;

        // is_bool: push bool var or arith var
        // for bool var: push pure bool index
        // for airth var: push arith index
        void push_assigned_var(hybrid_var x, bool is_bool);
        

        hybrid_var get_stage_var(stage x) const;
        void pop_last_var();

        var vsids_select(bool & is_bool);
        void bump_conflict_hybrid_vars();
        void hybrid_decay_act();

        // for bool var: atom index
        void do_watched_clauses(hybrid_var x, bool is_bool);
        // for bool var: atom index
        void undo_watched_clauses(hybrid_var x, bool is_bool);

        void find_next_process_clauses(var x, bool_var b, clause_vector & clauses, search_mode m_search_mode);

        void del_bool(bool_var b);
        void del_clauses();
        void register_atom(atom const * a);

        void clause_bump_act(clause & cls);
        void clause_decay_act();

        void reset_conflict_vars();
        void insert_conflict_from_bool(bool_var b);
        void insert_conflict_from_literals(unsigned sz, literal const * ls);

        var find_stage(hybrid_var x, bool is_bool) const;
        var max_stage_literal(literal l) const;
        var max_stage_lts(unsigned sz, literal const * cls) const;
        bool all_assigned_bool_arith(bool_var b) const;
        bool same_stage_bool(bool_var b, stage x) const;
        bool same_stage_literal(literal l, stage x) const;
        var max_stage_var(atom const * a) const;
        var max_stage_poly(poly const * p) const;
        var max_stage_var_poly(poly const * p) const;
        var max_stage_or_unassigned_ps(polynomial_ref_vector const & ps) const;
        var max_stage_or_unassigned_literals(unsigned num, literal const * ls) const;
        var max_stage_or_unassigned_atom(atom const * a) const;
        
        hybrid_var max_assigned_var(unsigned sz, literal const * ls, bool & is_bool) const;

        var all_assigned_or_left_literal(bool_var b) const;

        std::ostream & display_assigned_vars(std::ostream & out) const;
        std::ostream & display_var_stage(std::ostream &) const;
    };
};