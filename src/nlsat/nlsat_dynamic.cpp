#include "nlsat/nlsat_dynamic.h"
#include "util/heap.h"
#include <iomanip>
#include <math.h>

namespace nlsat {
    struct Dynamic_manager::imp {
        /**
         * Basic Manager
         */
        anum_manager & m_am;
        pmanager & m_pm;
        solver & m_solver;

        /**
         * Assignment
         */
        assignment & m_assignment;
        const svector<lbool> & m_bvalues;

        // bool var | arith var
        hybrid_var_vector m_assigned_hybrid_vars;

        /**
         * Stage
         */
        var_vector m_find_stage;
        unsigned m_stage;

        /**
         * Clauses
         */
        unsigned m_num_clauses;
        const clause_vector & m_clauses;
        clause_vector & m_learned;
        dynamic_clause_vector m_dynamic_clauses;

        /**
         * Watch
         */
        var_vector_vector m_hybrid_var_watched_clauses;
        var_vector_vector m_hybrid_var_unit_clauses;
        var_vector_vector m_hybrid_var_assigned_clauses;

        /**
         * Atoms
         */
        unsigned m_num_atoms;
        const atom_vector & m_atoms;
        dynamic_atom_vector m_dynamic_atoms;

        /**
         * var activity
         */
        unsigned m_num_vars;
        unsigned m_num_bool;
        unsigned m_num_hybrid;
        // pure bool index --> atom index
        const bool_var_vector & m_pure_bool_vars;
        // atom index --> pure bool index
        const bool_var_vector & m_pure_bool_convert;

        // bump: the quantum of increase when learning a clause
        double var_bump = 1;
        double bool_var_bump = 1; 
        // decay_factor: activities of all variables are multiplied by a constant
        const double var_decay = 0.95;
        const double bool_var_decay = 0.95;
        // init var activity randomly or not
        const bool rand_init_act = false;
        var_table m_conflict_arith;
        var_table m_conflict_bool;
        // bool var | arith var
        double_vector m_hybrid_activity;

        struct var_order {
            const double_vector & m_activity;
            var_order(double_vector const & vec): m_activity(vec) {}
            bool operator()(var v1, var v2) const {
                return m_activity[v1] == m_activity[v2] ? v1 < v2 : m_activity[v1] > m_activity[v2];
            }
        };

        heap<var_order> m_hybrid_heap;

        /**
         * learnt clause activity
         */
        double cls_bump = 1;
        const double cls_decay = 0.999;

        /**
         * Restart
         */
        // The initial restart limit
        int restart_first = 100;
        // The factor with which the restart limit is multiplied in each restart
        double    restart_inc = 1.5;
        // use luby restart sequence or not
        const bool luby_restart = false;
        int nof_conflicts;
        unsigned curr_conflicts;
        unsigned curr_lt_assign;
        unsigned & m_restart;
        unsigned & m_learned_deleted;

        /**
         * Learnt clause management
         */
        // The intitial limit for learnt clauses is a factor of the original clauses
        double    learntsize_factor = 1.0/3;
        // The limit for learnt clauses is multiplied with this factor each restart
        double    learntsize_inc = 1.1;
        // Minimum number to set the learnts limit to.
        const unsigned min_learnt_lim = 1;

        double max_learnts;
        double learntsize_adjust_confl;
        int learntsize_adjust_cnt;
        const unsigned learntsize_adjust_start_confl = 100;
        const double learntsize_adjust_inc = 1.5;
        
        imp(anum_manager & am, pmanager & pm, assignment & ass,  svector<lbool> const & bvalues, bool_var_vector const & pure_bool_vars, bool_var_vector const & pure_bool_convert, solver & s, clause_vector const & clauses, clause_vector & learned, atom_vector const & atoms, 
        unsigned & restart, unsigned & deleted)
        : m_am(am), m_pm(pm), m_assignment(ass), m_clauses(clauses), m_learned(learned), m_atoms(atoms), m_hybrid_heap(200, var_order(m_hybrid_activity)),
        m_restart(restart), m_solver(s), m_learned_deleted(deleted), m_bvalues(bvalues), m_pure_bool_vars(pure_bool_vars), m_pure_bool_convert(pure_bool_convert)
        {}

        ~imp(){

        }

        void set_var_num(unsigned x){
            DTRACE(tout << "start of set var num\n";);
            m_num_vars = x;
            init_pure_bool();
            make_space();
            collect_vars();
            set_watch();
            DTRACE(tout << "end of set var num\n";);
        }

        void init_pure_bool(){
            m_num_bool = m_pure_bool_vars.size();
            m_num_hybrid = m_num_vars + m_num_bool;
            DTRACE(tout << "num of bool: " << m_num_bool << std::endl;
                tout << "num of arith: " << m_num_vars << std::endl;
                tout << "num of hybrid: " << m_num_hybrid << std::endl;
            );
        }

        void make_space(){
            m_num_atoms = m_atoms.size();
            m_num_clauses = m_clauses.size();
            // m_var_activity.resize(m_num_vars, 0.0);
            m_hybrid_activity.resize(m_num_hybrid);
            m_hybrid_var_watched_clauses.resize(m_num_hybrid, var_vector());
            m_hybrid_var_unit_clauses.resize(m_num_hybrid, var_vector());
            m_hybrid_var_assigned_clauses.resize(m_num_hybrid, var_vector());
            m_hybrid_heap.set_bounds(m_num_hybrid);
            m_find_stage.resize(m_num_vars, null_var);
        }

        // set hybrid var watch for each clause
        void set_watch(){
            DTRACE(tout << "start of set watch\n";);
            for(clause_index i = 0; i < m_num_clauses; i++){
                dynamic_clause * cls = m_dynamic_clauses[i];
                // no bool var and no arith var
                if(cls->m_vars.empty() && cls->m_bool_vars.empty()){
                    cls->set_watched_var(null_var, null_var);
                }
                // one hybrid var, unit and no watch
                else if(cls->m_vars.size() + cls->m_bool_vars.size() == 1){
                    if(cls->m_vars.empty()){
                        SASSERT(cls->m_bool_vars.size() == 1);
                        hybrid_var x = *(cls->m_bool_vars.begin());
                        m_hybrid_var_unit_clauses[x].push_back(i);
                        cls->set_watched_var(null_var, null_var);
                    }
                    else if(cls->m_bool_vars.empty()) {
                        SASSERT(cls->m_vars.size() == 1);
                        hybrid_var x = *(cls->m_vars.begin()) + m_num_bool;
                        m_hybrid_var_unit_clauses[x].push_back(i);
                        cls->set_watched_var(null_var, null_var);
                    }
                    else {
                        UNREACHABLE();
                    }
                }
                // more hybrid vars, watch
                else {
                    // no arith var, peek two bool vars
                    if(cls->m_vars.empty()){
                        SASSERT(cls->m_bool_vars.size() >= 2);
                        // two bool vars
                        auto it = cls->m_bool_vars.begin();
                        hybrid_var x = *it, y = *(++it);
                        cls->set_watched_var(x, y);
                        m_hybrid_var_watched_clauses[x].push_back(i);
                        m_hybrid_var_watched_clauses[y].push_back(i);
                    }
                    // one arith var, peek one arith var and one bool var
                    else if(cls->m_vars.size() == 1){
                        SASSERT(cls->m_bool_vars.size() >= 1);
                        // bool var
                        hybrid_var x = *(cls->m_bool_vars.begin());
                        // arith var
                        hybrid_var y = *(cls->m_vars.begin()) + m_num_bool;
                        cls->set_watched_var(x, y);
                        m_hybrid_var_watched_clauses[x].push_back(i);
                        m_hybrid_var_watched_clauses[y].push_back(i);
                    }
                    // more arith vars, peek two arith vars
                    else {
                        SASSERT(cls->m_vars.size() >= 2);
                        // two arith vars
                        auto it = cls->m_vars.begin();
                        hybrid_var x = (*it) + m_num_bool;
                        it++;
                        hybrid_var y = (*it) + m_num_bool;
                        cls->set_watched_var(x, y);
                        m_hybrid_var_watched_clauses[x].push_back(i);
                        m_hybrid_var_watched_clauses[y].push_back(i);
                    }
                }
            }
            DTRACE(tout << "after set watch, display watch clauses\n";
                display_clauses_watch(tout);
                display_unit_clauses(tout);
                display_assigned_clauses(tout);
            );
            DTRACE(tout << "end of set watch\n";);
        }

        // collect arith var and bool var for each clause
        // bool var: pure bool index
        void collect_vars(){
            m_dynamic_atoms.reset();
            m_dynamic_clauses.reset();
            for(atom_index i = 0; i < m_atoms.size(); i++){
                var_table vars;
                collect_atom_vars(m_atoms[i], vars);
                m_dynamic_atoms.push_back(new dynamic_atom(i, m_atoms[i], vars));
            }
            for(clause_index i = 0; i < m_clauses.size(); i++){
                var_table vars;
                collect_clause_vars(m_clauses[i], vars);
                bool_var_table bool_vars;
                collect_clause_bool_vars(m_clauses[i], bool_vars);
                m_dynamic_clauses.push_back(new dynamic_clause(i, m_clauses[i], vars, bool_vars));
            }
        }

        void collect_atom_vars(atom const * a, var_table & vars){
            vars.reset();
            if(a == nullptr){
                return;
            }
            if(a->is_ineq_atom()){
                collect_ineq_vars(to_ineq_atom(a), vars);
            } 
            else {
                collect_root_vars(to_root_atom(a), vars);
            }
        }

        void collect_ineq_vars(ineq_atom const * a, var_table & vars){
            SASSERT(a != nullptr);
            for(unsigned i = 0; i < a->size(); i++){
                var_vector curr;
                m_pm.vars(a->p(i), curr);
                for(var v: curr){
                    vars.insert_if_not_there(v);
                }
            }
        }

        void collect_root_vars(root_atom const * a, var_table & vars){
            SASSERT(a != nullptr);
            var_vector curr;
            m_pm.vars(a->p(), curr);
            for(var v: curr){
                vars.insert_if_not_there(v);
            }
            vars.insert_if_not_there(a->x());
        }

        // collected bool vars are converted bool index
        void collect_clause_bool_vars(clause const * cls, bool_var_table & bool_vars){
            bool_vars.reset();
            for(literal l: *cls){
                if(m_atoms[l.var()] == nullptr){
                    bool_vars.insert_if_not_there(m_pure_bool_convert[l.var()]);
                }
            }
        }

        void collect_clause_vars(clause const * cls, var_table & vars){
            vars.reset();
            for(literal l: *cls){
                bool_var b = l.var();
                dynamic_atom const * curr = m_dynamic_atoms[b];
                for(var v: curr->m_vars){
                    vars.insert_if_not_there(v);
                }
            }
        }

        void init_learnt_management(){
            max_learnts = m_clauses.size() * learntsize_factor;
            if(max_learnts < min_learnt_lim){
                max_learnts = min_learnt_lim;
            }
            learntsize_adjust_confl = learntsize_adjust_start_confl;
            learntsize_adjust_cnt = (int) learntsize_adjust_confl;
        }

        void update_learnt_management(){
            if(--learntsize_adjust_cnt == 0){
                learntsize_adjust_confl *= learntsize_adjust_inc;
                learntsize_adjust_cnt = (int) learntsize_adjust_confl;
                max_learnts *= learntsize_inc;
            }
        }

        void init_nof_conflicts(){
            double rest_base = luby_restart ? luby(restart_inc, m_restart) : std::pow(restart_inc, m_restart);
            nof_conflicts = rest_base * restart_first;
        }

        static double luby(double y, int x){
            // Find the finite subsequence that contains index 'x', and the
            // size of that subsequence:
            int size, seq;
            for(size = 1, seq = 0; size < x+1; seq++, size = 2*size+1);
            while(size-1 != x){
                size = (size-1)>>1;
                seq--;
                x = x % size;
            }
            return std::pow(y, seq);
        }

        void minimize_learned(){
            if(m_learned.size() - curr_lt_assign >= max_learnts){
                unsigned sz1 = m_learned.size();
                TRACE("wzh", std::cout << "[reduce] enter reduceDB" << std::endl;
                    std::cout << "size: " << m_learned.size() << std::endl;
                );
                remove_learnt_act();
                unsigned sz2 = m_learned.size();
                double ratio = 100.0 * sz2 / sz1;
                TRACE("wzh", std::cout << "[reduce] exit reduceDB" << std::endl;
                    std::cout << "size: " << m_learned.size() << std::endl;
                    std::cout << "size shrink " << std::setprecision(2) << ratio << "%" << std::endl;
                );
                m_learned_deleted += (sz1 - sz2);
            }
        }

        // Comparator for reduceDB
        struct reduceDB_lt {
            bool operator()(clause const * cls1, clause const * cls2){
                return cls1->size() > 2 && (cls2->size() <= 2 || cls1->get_activity() < cls2->get_activity());
            }
        };

        void remove_learnt_act(){
            if(m_learned.size() <= 10){
                TRACE("wzh", tout << "[dynamic] learned size is too small: " << m_learned.size() << std::endl;);
                return;
            }
            TRACE("wzh", tout << "remove learnt clauses take effect" << std::endl;);

            double extra_lim = cls_bump / m_learned.size();
            TRACE("wzh", tout << "[reduce] extra limit is " << extra_lim << std::endl;);
            /**
            * Don't delete binary clauses. From the rest, delete clauses from the first half
            * and clauses with activity smaller than 'extra_lim':
            */
           std::sort(m_learned.begin(), m_learned.end(), reduceDB_lt());
           unsigned j = 0;
           for(unsigned i = 0; i < m_learned.size(); i++){
               if(m_learned[i]->size() > 2 && (i < m_learned.size() / 2 || m_learned[i]->get_activity() < extra_lim)){
                   m_solver.del_clause(m_learned[i]);
               }
               else{
                   m_learned[j++] = m_learned[i];
               }
           }
           m_learned.shrink(j);
        }

        void reset_curr_conflicts(){
            curr_conflicts = 0;
        }

        void inc_curr_conflicts(){
            curr_conflicts++;
        }

        void insert_conflict_from_bool(bool_var b){
            for(var v: m_dynamic_atoms[b]->m_vars){
                m_conflict_arith.insert_if_not_there(v);
            }
            if(m_atoms[b] == nullptr){
                m_conflict_bool.insert_if_not_there(m_pure_bool_convert[b]);
            }
        }

        void insert_conflict_from_literals(unsigned sz, literal const * ls){
            for(unsigned i = 0; i < sz; i++){
                literal l = ls[i];
                insert_conflict_from_bool(l.var());
            }
        }

        void reset_curr_literal_assign(){
            curr_lt_assign = 0;
        }

        void inc_curr_literal_assign(){
            curr_lt_assign++;
        }

        bool check_restart_requirement(){
            return nof_conflicts >= 0 && curr_conflicts >= nof_conflicts;
        }

        // Initialize
        void init_search(){
            DTRACE(tout << "dynamic init search\n";);
            m_find_stage.resize(m_num_vars, null_var);
            m_hybrid_heap.set_bounds(m_num_hybrid);
            rebuild_var_heap();
            m_stage = 0;
        }

        // rebuild hybrid var heap
        // pure bool var and arith var
        // pure bool var | arith var + m_num_bool
        void rebuild_var_heap(){
            m_hybrid_heap.clear();
            for(hybrid_var v = 0; v < m_num_hybrid; v++){
                m_hybrid_heap.insert(v);
            }
        }

        void hybrid_decay_act(){
            var_decay_act();
            bool_var_decay_act();
        }

        void var_decay_act(){
            TRACE("wzh", tout << "[mvsids] decay inc for var vsids: \n";
                 tout << var_bump << " -> " << var_bump * (1 / var_decay) << std::endl;           
            );
            var_bump *= (1 / var_decay);
        }

        void bool_var_decay_act(){
            TRACE("wzh", tout << "[mvsids] decay inc for bool_var vsids: \n";
                 tout << bool_var_bump << " -> " << bool_var_bump * (1 / bool_var_decay) << std::endl;           
            );
            bool_var_bump *= (1 / bool_var_decay);
        }

        void bump_conflict_hybrid_vars(){
            for(var v: m_conflict_arith){
                var_bump_act(v);
            }
            for(bool_var b: m_conflict_bool){
                bool_var_bump_act(b);
            }
        }

        void var_bump_act(var v){
            TRACE("wzh", tout << "[dynamic] bump activity for var " << v << std::endl;);
            var_bump_act(v, var_bump);
        }

        void bool_var_bump_act(bool_var b){
            bool_var_bump_act(b, bool_var_bump);
        }

        void var_bump_act(var v, double inc){
            v = v + m_num_bool;
            if((m_hybrid_activity[v] += inc) > 1e100){
                // Rescale:
                for(hybrid_var i = m_num_bool; i < m_num_hybrid; i++){
                    m_hybrid_activity[i] *= 1e-100;
                }
                var_bump *= 1e-100;
            }
            if(m_hybrid_heap.contains(v)){
                m_hybrid_heap.decreased(v);
            }
        }

        // pure bool index
        void bool_var_bump_act(bool_var b, double inc){
            if((m_hybrid_activity[b] += inc) > 1e100){
                // Rescale:
                for(hybrid_var i = 0; i < m_num_bool; i++){
                    m_hybrid_activity[i] *= 1e-100;
                }
                bool_var_bump *= 1e-100;
            }
            if(m_hybrid_heap.contains(b)){
                m_hybrid_heap.decreased(b);
            }
        }

        void clause_decay_act(){
            TRACE("wzh", tout << "[mvsids] decay inc for clause vsids: \n";
                 tout << cls_bump << " -> " << cls_bump * (1 / cls_decay) << std::endl;           
            );
            cls_bump *= (1 / cls_decay);
        }

        void clause_bump_act(clause & cls){
            clause_bump_act(cls, cls_bump);
        }

        void clause_bump_act(clause & cls, double inc){
            SASSERT(cls.is_learned());
            cls.set_activity(cls.get_activity() + inc);
            if(cls.get_activity() > 1e20){
                for(unsigned j = 0; j < m_learned.size(); j++){
                    m_learned[j]->set_activity(m_learned[j]->get_activity() * 1e-20);
                }
                cls_bump *= 1e-20;
            }
        }

        unsigned assigned_size() const {
            return m_assigned_hybrid_vars.size();
        }

        // bool_var: return pure bool index
        hybrid_var get_last_assigned_hybrid_var(bool & is_bool) const {
            if(m_assigned_hybrid_vars.empty()){
                is_bool = false;
                return null_var;
            }
            hybrid_var res = m_assigned_hybrid_vars.back();
            if(is_arith_var(res)){
                is_bool = false;
                return res - m_num_bool;
            }
            else {
                is_bool = true;
                return res;
            }
        }

        var get_last_assigned_arith_var() const {
            for(int i = m_assigned_hybrid_vars.size() - 1; i >= 0; i--){
                if(is_arith_var(m_assigned_hybrid_vars[i])){
                    return m_assigned_hybrid_vars[i] - m_num_bool;
                }
            }
            return null_var;
        }

        bool_var get_last_assigned_bool_var() const {
            for(int i = m_assigned_hybrid_vars.size() - 1; i >= 0; i--){
                if(is_bool_var(m_assigned_hybrid_vars[i])){
                    return m_assigned_hybrid_vars[i];
                }
            }
            return null_var;
        }

        hybrid_var get_stage_var(var x) const {
            unsigned curr_stage = 0;
            for(unsigned i = 0; i < m_assigned_hybrid_vars.size(); i++){
                hybrid_var v = m_assigned_hybrid_vars[i];
                if(is_arith_var(v)){
                    if(curr_stage == x){
                        return v - m_num_bool;
                    }
                    curr_stage++;
                }
            }
            return null_var;
        }

        void pop_last_var(){
            if(!m_assigned_hybrid_vars.empty()){
                hybrid_var v = m_assigned_hybrid_vars.back();
                m_assigned_hybrid_vars.pop_back();
                if(v != null_var){
                    SASSERT(!m_hybrid_heap.contains(v));
                    m_hybrid_heap.insert(v);
                    if(is_arith_var(v)){
                        m_find_stage[v - m_num_bool] = null_var;
                        SASSERT(m_stage >= 1);
                        m_stage--;
                    }
                }
            }
            DTRACE(display_arith_stage(tout););
        }

        inline bool is_arith_var(hybrid_var x) const {
            return x >= m_num_bool;
        }

        inline bool is_bool_var(hybrid_var x) const {
            return x < m_num_bool;
        }

        // bool var: pure bool index
        // arith var: arith index
        void push_assigned_var(hybrid_var x, bool is_bool){
            if(x == null_var){
                m_assigned_hybrid_vars.push_back(null_var);
                return;
            }
            if(is_bool){
                m_assigned_hybrid_vars.push_back(x);
            }
            else {
                m_assigned_hybrid_vars.push_back(x + m_num_bool);
                m_find_stage[x] = m_stage;
                m_stage++;
            }
            DTRACE(display_arith_stage(tout););
        }

        // is_bool: returned var is bool var or not
        // for bool var: return atom index
        // for arith var: return arith index
        hybrid_var vsids_select(bool & is_bool){
            DTRACE(m_hybrid_heap.display(tout););
            SASSERT(!m_hybrid_heap.empty());
            hybrid_var v = m_hybrid_heap.erase_min();
            if(v < m_num_bool){
                is_bool = true;
                return m_pure_bool_vars[v];
            }
            else {
                is_bool = false;
                return v - m_num_bool;
            }
        }

        // bool_var: atom index
        void find_next_process_clauses(var x, bool_var b, clause_vector & res, search_mode m_mode){
            res.reset();
            // exactly one null_var
            hybrid_var v;
            if(m_mode == BOOL){
                v = m_pure_bool_convert[b];
            }
            else if(m_mode == ARITH){
                v = x + m_num_bool;
            }
            else {
                UNREACHABLE();
            }
            // clause
            for(auto ele: m_hybrid_var_unit_clauses[v]){
                res.push_back(m_clauses[ele]);
            }
            // learned
            for(unsigned i = 0; i < m_learned.size(); i++){
                clause * cls = m_learned[i];
                if(only_left_clause(*cls, v)){
                    res.push_back(cls);
                }
            }
        }

        // only left this hybrid var unassigned
        bool only_left_clause(clause const & cls, hybrid_var x) const {
            return x < m_num_bool ? only_left_clause_bool(cls, x) : only_left_clause_arith(cls, x - m_num_bool);
        }

        // only left this bool var unassigned
        bool only_left_clause_bool(clause const & cls, bool_var b) const {
            bool have_only = false;
            for(literal l: cls){
                // bool literal
                if(m_atoms[l.var()] == nullptr){
                    if(l.var() == b){
                        have_only = true;
                    }
                    else {
                        // unassigned other bool_var
                        if(!m_assigned_hybrid_vars.contains(l.var())){
                            return false;
                        }
                    }
                }
                // arith literal
                else {
                    if(!all_assigned_bool_arith(l.var())){
                        return false;
                    }
                }
            }
            return have_only;
        }

        // only left this arith var unassigned
        bool only_left_clause_arith(clause const & cls, var x) const {
            bool have_only = false;
            for(literal l: cls){
                // bool literal
                if(m_atoms[l.var()] == nullptr){
                    // unassigned bool literal
                    if(!m_assigned_hybrid_vars.contains(l.var())){
                        return false;
                    }
                }
                // arith literal
                else {
                    // all assigned
                    if(all_assigned_bool_arith(l.var())){
                        continue;
                    }
                    // only this var unassigned
                    if(only_left_literal_arith(l, x)){
                        have_only = true;
                        continue;
                    }
                    // otherwise
                    return false;
                }
            }
            return have_only;
        }

        // check whether the arith literal is all assigned
        bool all_assigned_bool_arith(bool_var b) const {
            dynamic_atom const * a = m_dynamic_atoms[b];
            for(var v: a->m_vars){
                if(!m_assignment.is_assigned(v)){
                    return false;
                }
            }
            return true;
        }

        bool only_left_literal_arith(literal l, var x) const {
            return only_left_atom_arith(m_atoms[l.var()], x);
        }

        bool only_left_atom_arith(atom const * a, var x) const {
            if(a == nullptr){
                return false;
            }
            return a->is_ineq_atom() ? only_left_ineq_arith(to_ineq_atom(a), x) : only_left_and_ordered_root_arith(to_root_atom(a), x);
        }

        bool only_left_ineq_arith(ineq_atom const * a, var x) const {
            SASSERT(a != nullptr);
            bool contains = false;
            dynamic_atom const * curr = m_dynamic_atoms[a->bvar()];
            for(var v: curr->m_vars){
                if(v == x){
                    contains = true;
                    continue;
                }
                if(!m_assignment.is_assigned(v)){
                    return false;
                }
            }
            return contains;
        }

        bool only_left_and_ordered_root_arith(root_atom const * a, var x) const {
            SASSERT(!m_assignment.is_assigned(x));
            SASSERT(a != nullptr);
            // if we do not leave only x(), disable this atom
            if(a->x() != x){
                return false;
            }
            dynamic_atom const * curr = m_dynamic_atoms[a->bvar()];
            for(var v: curr->m_vars){
                if(v == x){
                    continue;
                }
                if(!m_assignment.is_assigned(v)){
                    return false;
                }
            }
            return true;
        }

        void del_bool(bool_var b){
            SASSERT(b < m_dynamic_atoms.size());
            m_dynamic_atoms[b]->~dynamic_atom();
        }

        void del_clauses(){
            m_dynamic_clauses.reset();
        }

        void register_atom(atom const * a){
            SASSERT(a != nullptr);
            while(a->bvar() >= m_dynamic_atoms.size()){
                m_dynamic_atoms.push_back(nullptr);
            }
            var_table vars;
            collect_atom_vars(a, vars);
            m_dynamic_atoms[a->bvar()] = new dynamic_atom(a->bvar(), a, vars);
        }

        // is_bool: bool var or not
        // for bool var: x is index of m_atoms
        void do_watched_clauses(hybrid_var x, bool is_bool){
            DTRACE(tout << "do watched clauses for hybrid var " << x << std::endl;);
            unsigned j = 0;
            // bool var
            if(is_bool){
                x = m_pure_bool_convert[x];
            }
            // arith var
            else {
                x = x + m_num_bool;
            }
            // watched clauses ==> unit clauses
            for(clause_index idx: m_hybrid_var_watched_clauses[x]){
                // ignore unit var clauses
                if(unit_clause_contains(idx)){
                    m_hybrid_var_watched_clauses[x][j++] = idx;
                    continue;
                }
                dynamic_clause * cls = m_dynamic_clauses[idx];
                hybrid_var other = cls->get_another_watched_var(x);
                hybrid_var next = select_watched_var_except(cls, other);
                if(next == null_var){
                    // unit clause to other
                    m_hybrid_var_unit_clauses[other].push_back(idx);
                    // still watch
                    m_hybrid_var_watched_clauses[x][j++] = idx;
                }
                else{
                    // change watch
                    m_hybrid_var_watched_clauses[next].push_back(idx);
                    cls->set_watched_var(other, next);
                }
            }
            m_hybrid_var_watched_clauses[x].shrink(j);
            j = 0;
            // unit clauses ==> assigned clauses
            for(auto ele: m_hybrid_var_unit_clauses[x]){
                m_hybrid_var_assigned_clauses[x].push_back(ele);
            }
            m_hybrid_var_unit_clauses[x].reset();
            DTRACE(tout << "after do watch clauses, display watch clauses\n";
                display_clauses_watch(tout);
                display_unit_clauses(tout);
                display_assigned_clauses(tout);
            );
        }

        bool unit_clause_contains(clause_index idx) const {
            for(auto ele: m_hybrid_var_unit_clauses){
                if(ele.contains(idx)){
                    return true;
                }
            }
            return false;
        }

        inline std::string bool2str(bool b) const {
            return b ? "true" : "false";
        }

        hybrid_var select_watched_var_except(dynamic_clause const * cls, hybrid_var x){
            bool is_arith;
            if(is_arith_var(x)){
                is_arith = true;
                x = x - m_num_bool;
            }
            else {
                is_arith = false;
            }
            for(bool_var b: cls->m_bool_vars){
                if(!is_arith && b == x){
                    continue;
                }
                // not assigned yet
                if(m_bvalues[m_pure_bool_vars[b]] == l_undef){
                    return b;
                }
            }
            for(var v: cls->m_vars){
                if(is_arith && v == x){
                    continue;
                }
                // not assigned yet
                if(!m_assignment.is_assigned(v)){
                    // return hybrid var
                    return v + m_num_bool;
                }
            }
            return null_var;
        }

        // x is hybrid var
        bool clause_contains_hybrid_var(dynamic_clause const * cls, hybrid_var x, bool is_bool) const {
            DTRACE(tout << "here1\n";);
            if(!is_bool){
                x = x - m_num_bool;
                for(var v: cls->m_vars){
                    if(v == x){
                        DTRACE(tout << "here2\n";);
                        return true;
                    }
                }
            }
            else {
                for(bool_var b: cls->m_bool_vars){
                    if(b == x){
                        DTRACE(tout << "here3\n";);
                        return true;
                    }
                }
            }
            DTRACE(tout << "here4\n";);
            return false;
        }

        // is_bool: bool var or not
        // for bool var: x is index of m_atoms
        void undo_watched_clauses(hybrid_var x, bool is_bool){
            DTRACE(tout << "undo watched clauses for hybrid var " << x << std::endl;
                tout << "is bool: " << bool2str(is_bool) << std::endl;
            );
            if(is_bool){
                x = m_pure_bool_convert[x];
            }
            else {
                x = x + m_num_bool;
            }
            DTRACE(tout << "debug1\n";);
            // delete unit clauses
            unsigned j = 0;
            for(hybrid_var v = 0; v < m_hybrid_var_unit_clauses.size(); v++){
                j = 0;
                for(unsigned i = 0; i < m_hybrid_var_unit_clauses[v].size(); i++){
                    dynamic_clause * cls = m_dynamic_clauses[m_hybrid_var_unit_clauses[v][i]];
                    if(!clause_contains_hybrid_var(cls, x, is_bool)){
                        m_hybrid_var_unit_clauses[v][j++] = m_hybrid_var_unit_clauses[v][i];
                    }
                }
                m_hybrid_var_unit_clauses[v].shrink(j);
            }
            // m_unit_var_clauses.shrink(j);
            DTRACE(tout << "debug2\n";
                tout << m_num_hybrid << std::endl;
                tout << x << std::endl;
            );
            // assigned clauses ==> unit clauses
            j = 0;
            for(auto ele: m_hybrid_var_assigned_clauses[x]){
                m_hybrid_var_unit_clauses[x].push_back(ele);
            }
            m_hybrid_var_assigned_clauses[x].reset();
            DTRACE(tout << "after undo watch clauses, display watch clauses\n";
                display_clauses_watch(tout);
                display_unit_clauses(tout);
                display_assigned_clauses(tout);
            );
        }

        void reset_conflict_vars(){
            m_conflict_arith.reset();
            m_conflict_bool.reset();
        }

        var find_stage(var x) const {
            if(x == null_var){
                return null_var;
            }
            if(x < m_find_stage.size()){
                return m_find_stage[x];
            }
            return null_var;
        }

        bool same_stage_bool(bool_var b, var x) const {
            // for all bool literal, we return true
            if(m_atoms[b] == nullptr){
                // return x == null_var;
                return true;
            }
            dynamic_atom const * curr = m_dynamic_atoms[b];
            var stage = find_stage(x);
            bool contain = false;
            for(var v: curr->m_vars){
                if(v == x){
                    contain = true;
                }
                else {
                    var stage2 = find_stage(v);
                    if(stage2 > stage){
                        return false;
                    }
                }
            }
            return contain;
        }

        bool same_stage_literal(literal l, var x) const {
            return same_stage_bool(l.var(), x);
        }

        var max_stage_poly(poly const * p) const {
            var_vector curr;
            m_pm.vars(p, curr);
            var x = 0;
            for(var v: curr){
                var curr_stage = find_stage(v);
                if(x == 0 || curr_stage > x){
                    x = curr_stage;
                }
                if(x == null_var){
                    return null_var;
                }
            }
            return x;
        }

        var max_stage_var_poly(poly const * p) const {
            var_vector curr;
            m_pm.vars(p, curr);
            var res_x = 0, max_stage = 0;
            for(var v: curr){
                var curr_stage = find_stage(v);
                if(max_stage == 0 || curr_stage > max_stage){
                    max_stage = curr_stage;
                    res_x = v;
                }
                // TRACE("wzh", tout << "[debug] var " << v << " stage " << curr_stage << std::endl;);
            }
            return res_x;
        }

        var max_stage_bool(bool_var b) const {
            if(m_atoms[b] == nullptr){
                return null_var;
            }
            dynamic_atom const * curr = m_dynamic_atoms[b];
            var res = 0;
            for(var v: curr->m_vars){
                var curr = find_stage(v);
                if(res == 0 || curr > res){
                    res = curr;
                    if(res == null_var){
                        return null_var;
                    }
                }
            }
            return res;
        }

        var max_stage_lts(unsigned sz, literal const * cls) const {
            var x = 0;
            bool all_bool = true;
            for (unsigned i = 0; i < sz; i++) {
                literal l = cls[i];
                if (m_atoms[l.var()] != nullptr) {
                    var y = max_stage_literal(l);
                    if (x == 0 || y > x){
                        x = y;
                    }
                    all_bool = false;
                }
            }
            return all_bool ? null_var : x;
        }

        var max_stage_literal(literal l) const {
            return max_stage_bool(l.var());
        }

        var max_stage_var(atom const * a) const {
            dynamic_atom const * curr = m_dynamic_atoms[a->bvar()];
            if(curr->m_vars.empty()){
                return null_var;
            }
            var res = *(curr->m_vars.begin()), max_stage = find_stage(res);
            for(var cur: curr->m_vars){
                var curr_stage = find_stage(cur);
                if(curr_stage > max_stage){
                    max_stage = curr_stage;
                    res = cur;
                }
            }
            return res;
        }

        void get_vars_ps(polynomial_ref_vector const & ps, var_table & vec) const {
            vec.reset();
            for(unsigned i = 0; i < ps.size(); i++){
                var_vector curr;
                poly * p = ps.get(i);
                m_pm.vars(p, curr);
                for(var v: curr){
                    vec.insert_if_not_there(v);
                }
            }
        }

        var max_stage_or_unassigned_ps(polynomial_ref_vector const & ps) const {
            var_table curr_vars;
            get_vars_ps(ps, curr_vars);
            var max_stage = 0, res_x = null_var;
            for(var v: curr_vars){
                if(!m_assignment.is_assigned(v)){
                    return v;
                }
                var curr = find_stage(v);
                if(max_stage == 0 || curr > max_stage){
                    max_stage = curr;
                    res_x = v;
                }
            }
            return res_x;
        }

        void get_vars_literals(unsigned num, literal const * ls, var_table & vec) const {
            vec.reset();
            for(unsigned i = 0; i < num; i++){
                literal l = ls[i];
                for(var v: m_dynamic_atoms[l.var()]->m_vars){
                    vec.insert_if_not_there(v);
                }
            }
        }

        var max_stage_or_unassigned_literals(unsigned num, literal const * ls) const {
            var_table curr_vars;
            get_vars_literals(num, ls, curr_vars);
            var max_stage = 0, res_x = null_var;
            for(var v: curr_vars){
                if(!m_assignment.is_assigned(v)){
                    return v;
                }
                var curr_stage = find_stage(v);
                if(max_stage == 0 || curr_stage > max_stage){
                    max_stage = curr_stage;
                    res_x = v;
                }
            }
            return res_x;
        }

        var max_stage_or_unassigned_atom(atom const * a) const {
            var max_stage = 0, res_x = null_var;
            for(var v: m_dynamic_atoms[a->bvar()]->m_vars){
                if(!m_assignment.is_assigned(v)){
                    return v;
                }
                var curr_stage = find_stage(v);
                if(max_stage == 0 || curr_stage > max_stage){
                    max_stage = curr_stage;
                    res_x = v;
                }
            }
            return res_x;
        }
        
        /**
         * Display
         */
        std::ostream & display_clauses_watch(std::ostream & out) const {
            out << "display clauses watch\n";
            for(clause_index i = 0; i < m_dynamic_clauses.size(); i++){
                m_solver.display(out, *m_dynamic_clauses[i]->get_clause()) << std::endl;
                out << "(" << m_dynamic_clauses[i]->m_watched_var.first << ", " << m_dynamic_clauses[i]->m_watched_var.second << ")" << std::endl;
            }
            return out;
        }

        std::ostream & display_clause_vector(std::ostream & out, var_vector const & vec) const {
            for(auto ele: vec){
                m_solver.display(out, *m_clauses[ele]) << std::endl;
            }
            return out;
        }
        
        std::ostream & display_unit_clauses(std::ostream & out) const {
            out << "display unit clauses\n";
            for(hybrid_var v = 0; v < m_hybrid_var_unit_clauses.size(); v++){
                out << "unit to hybrid var " << v << std::endl;
                display_clause_vector(out, m_hybrid_var_unit_clauses[v]);
            }
            return out;
        }

        std::ostream & display_assigned_clauses(std::ostream & out) const {
            out << "display assigned clauses\n";
            for(hybrid_var v = 0; v < m_hybrid_var_assigned_clauses.size(); v++){
                out << "assigned to hybrid var " << v << std::endl;
                display_clause_vector(out, m_hybrid_var_assigned_clauses[v]);
            }
            return out;
        }

        std::ostream & display_arith_stage(std::ostream & out) const {
            out << "display arith stage\n";
            for(var v = 0; v < m_find_stage.size(); v++){
                out << "arith var " << v << ", stage: " << m_find_stage[v] << std::endl;
            }
            return out;
        }

        std::ostream & display_assigned_vars(std::ostream & out) const {
            out << "display assigned vars\n";
            if(m_assigned_hybrid_vars.empty()){
                out << "[EMPTY]\n";
            }
            else {
                for(auto ele: m_assigned_hybrid_vars) {
                    out << ele << " ";
                }
                out << std::endl;
            }
            return out;
        }
    };

    Dynamic_manager::Dynamic_manager(anum_manager & am, pmanager & pm, assignment & ass, svector<lbool> const & bvalues, bool_var_vector const & pure_bool_vars, bool_var_vector const & pure_bool_convert, solver & s, clause_vector const & clauses, clause_vector & learned, 
    atom_vector const & atoms, unsigned & restart, unsigned & deleted){
        m_imp = alloc(imp, am, pm, ass, bvalues, pure_bool_vars, pure_bool_convert, s, clauses, learned, atoms, restart, deleted);
    }

    Dynamic_manager::~Dynamic_manager(){
        DTRACE(tout << "dealloc dynamic manager\n";);
        dealloc(m_imp);
    }

    void Dynamic_manager::set_var_num(unsigned x){
        m_imp->set_var_num(x);
    }

    void Dynamic_manager::init_learnt_management(){
        m_imp->init_learnt_management();
    }

    void Dynamic_manager::update_learnt_management(){
        m_imp->update_learnt_management();
    }

    void Dynamic_manager::init_nof_conflicts(){
        m_imp->init_nof_conflicts();
    }

    void Dynamic_manager::minimize_learned(){
        m_imp->minimize_learned();
    }

    void Dynamic_manager::reset_curr_conflicts(){
        m_imp->reset_curr_conflicts();
    }

    void Dynamic_manager::reset_curr_literal_assign(){
        m_imp->reset_curr_literal_assign();
    }

    void Dynamic_manager::inc_curr_literal_assign(){
        m_imp->inc_curr_literal_assign();
    }

    bool Dynamic_manager::check_restart_requirement(){
        return m_imp->check_restart_requirement();
    }

    void Dynamic_manager::init_search(){
        m_imp->init_search();
    }

    unsigned Dynamic_manager::assigned_size() const {
        return m_imp->assigned_size();
    }

    var Dynamic_manager::get_stage_var(var x) const {
        return m_imp->get_stage_var(x);
    }

    void Dynamic_manager::pop_last_var(){
        m_imp->pop_last_var();
    }

    void Dynamic_manager::push_assigned_var(hybrid_var x, bool is_bool){
        m_imp->push_assigned_var(x, is_bool);
    }

    var Dynamic_manager::vsids_select(bool & is_bool){
        return m_imp->vsids_select(is_bool);
    }

    void Dynamic_manager::find_next_process_clauses(var x, bool_var b, clause_vector & clauses, search_mode mode){
        m_imp->find_next_process_clauses(x, b, clauses, mode);
    }

    void Dynamic_manager::del_bool(bool_var b){
        m_imp->del_bool(b);
    }

    void Dynamic_manager::del_clauses(){
        m_imp->del_clauses();
    }

    void Dynamic_manager::register_atom(atom const * a){
        m_imp->register_atom(a);
    }

    void Dynamic_manager::do_watched_clauses(var x, bool is_bool){
        m_imp->do_watched_clauses(x, is_bool);
    }

    void Dynamic_manager::undo_watched_clauses(var x, bool is_bool){
        m_imp->undo_watched_clauses(x, is_bool);
    }

    void Dynamic_manager::clause_bump_act(clause & cls){
        m_imp->clause_bump_act(cls);
    }

    void Dynamic_manager::reset_conflict_vars(){
        m_imp->reset_conflict_vars();
    }

    void Dynamic_manager::inc_curr_conflicts(){
        m_imp->inc_curr_conflicts();
    }

    void Dynamic_manager::insert_conflict_from_bool(bool_var b){
        m_imp->insert_conflict_from_bool(b);
    }

    void Dynamic_manager::insert_conflict_from_literals(unsigned sz, literal const * ls){
        m_imp->insert_conflict_from_literals(sz, ls);
    }

    void Dynamic_manager::bump_conflict_hybrid_vars(){
        m_imp->bump_conflict_hybrid_vars();
    }

    void Dynamic_manager::hybrid_decay_act(){
        m_imp->hybrid_decay_act();
    }

    void Dynamic_manager::clause_decay_act(){
        m_imp->clause_decay_act();
    }

    var Dynamic_manager::find_stage(var x) const {
        return m_imp->find_stage(x);
    }

    var Dynamic_manager::max_stage_literal(literal l) const {
        return m_imp->max_stage_literal(l);
    }

    var Dynamic_manager::max_stage_lts(unsigned sz, literal const * ls) const {
        return m_imp->max_stage_lts(sz, ls);
    }

    bool Dynamic_manager::all_assigned_bool_arith(bool_var b) const {
        return m_imp->all_assigned_bool_arith(b);
    }

    bool Dynamic_manager::same_stage_bool(bool_var b, var x) const {
        return m_imp->same_stage_bool(b, x);
    }

    bool Dynamic_manager::same_stage_literal(literal l, var x) const {
        return m_imp->same_stage_literal(l, x);
    }

    var Dynamic_manager::max_stage_var(atom const * a) const {
        return m_imp->max_stage_var(a);
    }

    var Dynamic_manager::max_stage_poly(poly const * p) const {
        return m_imp->max_stage_poly(p);
    }

    var Dynamic_manager::max_stage_var_poly(poly const * p) const {
        return m_imp->max_stage_var_poly(p);
    }

    var Dynamic_manager::max_stage_or_unassigned_ps(polynomial_ref_vector const & ps) const {
        return m_imp->max_stage_or_unassigned_ps(ps);
    }

    var Dynamic_manager::max_stage_or_unassigned_literals(unsigned num, literal const * ls) const {
        return m_imp->max_stage_or_unassigned_literals(num, ls);
    }

    var Dynamic_manager::max_stage_or_unassigned_atom(atom const * a) const {
        return m_imp->max_stage_or_unassigned_atom(a);
    }

    hybrid_var Dynamic_manager::get_last_assigned_hybrid_var(bool & is_bool) const {
        return m_imp->get_last_assigned_hybrid_var(is_bool);
    }

    std::ostream & Dynamic_manager::display_assigned_vars(std::ostream & out) const {
        return m_imp->display_assigned_vars(out);
    }
};