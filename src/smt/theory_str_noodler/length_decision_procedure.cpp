#include <queue>
#include <utility>
#include <algorithm>

#include <mata/nfa/strings.hh>

#include "util.h"
#include "aut_assignment.h"
#include "length_decision_procedure.h"

namespace smt::noodler {

    BasicTerm begin_of(zstring of, zstring from) {
        return BasicTerm(BasicTermType::Variable, "B!" + of.encode() + "_IN_" + from.encode());
    }

    bool VarConstraint::check_side(const Concat& side) {
        return side.size() == 1 && side[0].get_name() == _name;
    }

    void VarConstraint::emplace(const Concat& c, std::map<zstring, BasicTerm>& lit_conversion) {
        Concat n {};
        for (const BasicTerm& t : c) {
            if (BasicTermType::Literal == t.get_type()) {
                BasicTerm lit(BasicTermType::Literal, LengthDecisionProcedure::generate_lit_alias(t, lit_conversion));
                n.emplace_back(lit);
            } else {
                n.emplace_back(t);
            }
        }

        _constr_eqs.emplace_back(n);
    }

    bool VarConstraint::add(const Predicate& pred, std::map<zstring, BasicTerm>& lit_conversion) {
        if (check_side(pred.get_left_side())) {
            emplace(pred.get_right_side(), lit_conversion);
            return true;
        }
        if (check_side(pred.get_right_side())) {
            emplace(pred.get_left_side(), lit_conversion);
            return true;
        }

        // Fresh variable 
        emplace(pred.get_right_side(), lit_conversion);
        emplace(pred.get_left_side(), lit_conversion);

        return false;
    }

    const std::vector<zstring>& VarConstraint::get_lits() const {
        return _lits;
    }

    LenNode VarConstraint::generate_side_eq(const std::vector<LenNode>& side_len) {
        LenNode left = BasicTerm(BasicTermType::Variable, this->_name);
        // if there is no variable: length is 0, for one variable the length of the right side is its length, for more the length is their sum
        LenNode right = (side_len.size() == 0) ? LenNode(0)
            : ((side_len.size() == 1) ? LenNode(side_len[0]) : LenNode(LenFormulaType::PLUS, side_len));
        return LenNode(LenFormulaType::EQ, {left, right});
    }

    /**
     * @brief Compare first n characters of l1 with last n characters of l2 (e.g. l1=banana, l2=ababa, n=2 -> [ba]nana, aba[ba] -> true)
     * 
     * @return bool match of substrings
     */
    bool VarConstraint::zstr_comp(const zstring& l1_val, const zstring& l2_val, unsigned n) {
        int s1 = 0;
        int s2 = l2_val.length() - n;

        if (s2 < 0) {
            s1 -= s2;
            n += s2;
            s2 = 0;
        }
        if (s1 + n > l1_val.length()) {
            n = l1_val.length() - s1;
        }

        for (unsigned i = 0; i < n; i++) {
            if (l1_val[s1+i] != l2_val[s2+i]) {
                return false;
            }
        }

        return true;
    }

    LenNode VarConstraint::align_literals(const zstring& l1, const zstring& l2, const std::map<zstring, BasicTerm>& conv) {
        zstring l1_val = conv.at(l1).get_name();
        zstring l2_val = conv.at(l2).get_name();

        if (l1_val.length() == 1) {
            if (l2_val.length() == 1) {
                if (l1_val[0] == l2_val[0]) {
                    return LenNode(LenFormulaType::TRUE, {});
                } else {
                    return LenNode(LenFormulaType::NOT, {LenNode(LenFormulaType::EQ, {begin_of(l1, this->_name), begin_of(l2, this->_name)})});
                }
            }
        }

        std::vector<unsigned> overlays{};

        for (unsigned n = 1; n <= l2_val.length() + l1_val.length() - 1; ++n) {
            if (zstr_comp(l1_val, l2_val, n)) {
                overlays.emplace_back(n);
            }
        }

        LenNode before (LenFormulaType::LEQ, {LenNode(LenFormulaType::PLUS, {begin_of(l1, this->_name), rational(l1_val.length())}), begin_of(l2, this->_name)});
        LenNode after (LenFormulaType::LEQ, {LenNode(LenFormulaType::PLUS, {begin_of(l2, this->_name), rational(l2_val.length())}), begin_of(l1, this->_name)});
        std::vector<LenNode> align{before, after};
        for (unsigned i : overlays) {
            // b(l1) = b(l2) + |l2| - i
            align.emplace_back(LenNode(LenFormulaType::EQ, {
                LenNode(LenFormulaType::PLUS, {begin_of(l1, this->_name), rational(i)}),
                LenNode(LenFormulaType::PLUS, {begin_of(l2, this->_name), rational(l2_val.length())})
            }));
        }

        return LenNode(LenFormulaType::OR, align);
    }

    LenNode VarConstraint::get_lengths(const std::map<zstring,VarConstraint>& pool, const std::map<zstring,BasicTerm>& conv) {
        std::vector<LenNode> form{};

        // lits alignment
        for (const auto& a : _alignments) {
            form.emplace_back(align_literals(a.first, a.second, conv));
        }

        // kontys constraints e.g. x = uvw -> |x| = |u|+|v|+|w|
        // TODO: only generate restrictrions for length sensitive variables
        for (const Concat& side : _constr_eqs) {
            // bool unconstrained = true;    // there are unconstrained variables
            std::vector<LenNode> side_len {};

            for (const BasicTerm& t : side) {
                if (t.get_type() == BasicTermType::Literal) {
                    side_len.emplace_back(conv.at(t.get_name()));
                } else {
                    side_len.emplace_back(t);
                }
            }

            form.emplace_back(generate_side_eq(side_len));
        }

        // begin constraints
        for (const Concat& side : _constr_eqs) {
            BasicTerm last (BasicTermType::Length);

            for (const BasicTerm& t : side) {
                form.emplace_back(generate_begin(t.get_name(), last));
                if (t.get_type() == BasicTermType::Variable && pool.count(t.get_name())) {
                    for (const zstring& lit : pool.at(t.get_name()).get_lits()) {
                        form.emplace_back(generate_begin(lit, t.get_name()));
                    }
                }
                last = t;
            }
        }

        STRACE("str",
            tout << "Length constraints on variable " << this->_name << "\n-----\n";
            for (LenNode c : form) {
                tout << c << std::endl;
            }
            tout << "-----\n\n";
        );


        return LenNode(LenFormulaType::AND, form);
    }

    LenNode VarConstraint::generate_begin(const zstring& var_name, const BasicTerm& last, bool precise) {
        LenNode end_of_last = (last.get_type() == BasicTermType::Length)
            ? LenNode(0)
            : LenNode(LenFormulaType::PLUS, {begin_of(last.get_name(), this->_name), last});

        LenFormulaType ftype = precise ? LenFormulaType::EQ : LenFormulaType::LEQ;
        LenNode out = LenNode(ftype, {end_of_last, begin_of(var_name, this->_name)});
        
        return out;
    }

    LenNode VarConstraint::generate_begin(const zstring& lit, const zstring& from) {
        LenNode out (LenFormulaType::EQ, {begin_of(lit, this->_name), LenNode(LenFormulaType::PLUS, {begin_of(lit, from), begin_of(from, this->_name)})});
        return out;
    }

    bool VarConstraint::parse(std::map<zstring,VarConstraint>& pool, std::map<zstring,BasicTerm>& conv) {
        if (is_parsed == l_true) {
            return true;	// Already parsed
        }

        if (is_parsed == l_undef) {
            return false;	// Cycle
        }

        is_parsed = l_undef;	// Currently in parsing

        // parse derived
        for (const Concat& side : _constr_eqs) {
            std::vector<zstring> lits_in_side {};
            for (const BasicTerm& t : side) {
                if (t.get_type() == BasicTermType::Literal) {
                    lits_in_side.emplace_back(t.get_name());
                }
                if (t.get_type() == BasicTermType::Variable) {
                    // parse constrained variables
                    if (pool.count(t.get_name())) {
                        if (pool[t.get_name()].parse(pool, conv) == false) {
                            return false;	// There is a cycle
                        }

                        for (const zstring& lit : pool[t.get_name()].get_lits()) {
                            lits_in_side.emplace_back(lit);
                        }
                    }
                }
            }

            for (const zstring& l1 : _lits) {
                for (const zstring& l2 : lits_in_side) {
                    _alignments.emplace_back(l1, l2);
                }
            }

            for (const zstring& l : lits_in_side) {
                _lits.emplace_back(l);
            }
        }

        is_parsed = l_true;

        
        return true;
    }

    std::string VarConstraint::to_string() const {
        std::string ret = "#####\n# VarConstraint: " + _name.encode() + "\n###\n#";
        bool first = true;
        for (const Concat& side : _constr_eqs) {
            if (!first) {
                ret += " =";
            }
            first = false;

            for (const BasicTerm& term : side) {
                // Literals will be displayed just by their name, not by value
                ret += " " + term.to_string();
            }
        }

        ret += "\n###\n# lits:";

        for (const zstring& t :_lits) {
            // for explicit: ... lname ...
            ret += " " + t.encode(); // + ((t.parent_var == "") ? "" : ("("+t.parent_var.encode()+")"));
        }

        ret += "\n#####\n";
        return ret;
    }



    static std::ostream& operator<<(std::ostream& os, const VarConstraint& vc) {
        os << vc.to_string();
        return os;
    }

    zstring LengthDecisionProcedure::generate_lit_alias(const BasicTerm& lit, std::map<zstring, BasicTerm>& lit_conversion) {
        zstring new_lit_name = util::mk_noodler_var_fresh("lit").get_name();
        // lit_conversion[new_lit_name] = lit;
        lit_conversion.emplace(std::make_pair(new_lit_name, lit));
        return new_lit_name;
    }

    void LengthDecisionProcedure::add_to_pool(std::map<zstring, VarConstraint>& pool, const Predicate& pred) {
        bool in_pool = false;

        for (const Concat& side : pred.get_params()) {
            if (side.size() == 1 && side[0].get_type() == BasicTermType::Variable) {
                zstring var_name = side[0].get_name();
                if (pool.count(var_name) == 0) {
                    pool[var_name] = VarConstraint(var_name);
                }
                pool[var_name].add(pred, lit_conversion);

                in_pool = true;
            }
        }

        if (!in_pool) {
            zstring fresh = util::mk_noodler_var_fresh("f").get_name();
            pool[fresh] = VarConstraint(fresh);
            pool[fresh].add(pred, lit_conversion);
        }
    }


    ///////////////////////////////////

    lbool LengthDecisionProcedure::compute_next_solution() {
        STRACE("str", tout << "len: Compute next solution\n"; );

        STRACE("str",
            tout << " - formula after preprocess:\n";
            for (const Predicate& pred : this->formula.get_predicates()) {
                tout << "\t" << pred << std::endl;
            }
            tout << std::endl;
        );

        // Check for suitability
        std::vector<BasicTerm> concat_vars = {};	// variables that have appeared in concatenation 
        
        // TODO: compact to a function
        STRACE("str", tout << " - checking suitability: "; );
        for (const Predicate& pred : this->formula.get_predicates()) {
            if (!pred.is_equation()) {
                STRACE("str", tout << "False - Inequations\n");
                return l_undef;
            }
            for (const Concat& side : pred.get_params()) {
                if (side.size() <= 1) {
                    continue;
                }

                for (const BasicTerm& t : side) {
                    if (t.is_literal()) {
                        continue;
                    }

                    if (std::find(concat_vars.begin(), concat_vars.end(), t) == concat_vars.end()) {
                        concat_vars.emplace_back(t);
                        continue;
                    } else {
                        STRACE("str", tout << "False - multiconcat on " << t.to_string() << std::endl; );
                        return l_undef;
                    }

                    STRACE("str", tout << "False - regular constraitns on term " << t << std::endl; );
                    return l_undef;
                }
            }
        }
        // End check for suitability

        STRACE("str", tout << "True\n"; );

        std::map<zstring, VarConstraint> pool{};

        for (const Predicate& pred : this->formula.get_predicates()) {
            add_to_pool(pool, pred);
        }   

        STRACE("str",
            tout << "Conversions:\n-----\n";
            for (auto c : lit_conversion) {
                tout << c.first << " : " << c.second << std::endl;
            }
            tout << "-----\n";
        );  

        for (std::pair<zstring, VarConstraint> it : pool) {
            if (pool[it.first].parse(pool, lit_conversion) == false) {
                // There is a cycle
                STRACE("str", tout << "len: Cyclic dependecy.\n";);
                return l_undef;	// We cannot solve this formula
            }
        }

        // Change if there is filler var filter
        for (const BasicTerm& v : this->formula.get_vars()) {
            implicit_len_formula.emplace_back(LenNode(LenFormulaType::LEQ, {0, v}));
        }

        for (std::pair<zstring, VarConstraint> it : pool) {
            computed_len_formula.emplace_back(pool[it.first].get_lengths(pool, lit_conversion));
        }

        STRACE("str", tout << "len: Finished computing.\n");
        return l_true;
    }

    std::pair<LenNode, LenNodePrecision> LengthDecisionProcedure::get_lengths() {
        STRACE("str", tout << "len: Get lengths\n"; );
        LenNode len_formula = LenNode(LenFormulaType::AND, {
            this->preprocessing_len_formula, 
            LenNode(LenFormulaType::AND, this->implicit_len_formula), 
            LenNode(LenFormulaType::AND, this->computed_len_formula)
        });

        for (const auto& t : init_aut_ass) {
            BasicTerm term = t.first;
            std::set<smt::noodler::BasicTerm> vars_in_eqs = this->formula.get_vars();    // Variables in all predicates

            // term does not appear in any predicate
            if (vars_in_eqs.find(term) == vars_in_eqs.end()) {
                len_formula.succ.emplace_back(this->init_aut_ass.get_lengths(term));
            }
        }

        return {len_formula, this->precision};
    }

    void LengthDecisionProcedure::init_computation() {
    }

    lbool LengthDecisionProcedure::preprocess(PreprocessType opt, const BasicTermEqiv &len_eq_vars) {

        FormulaPreprocessor prep_handler(this->formula, this->init_aut_ass, this->init_length_sensitive_vars, m_params);

        STRACE("str", tout << "len: Preprocessing\n");

        prep_handler.remove_trivial();
        prep_handler.reduce_diseqalities(); // only makes variable a literal or removes the disequation 

        // Underapproximate if it contains inequations
        for (const BasicTerm& t : this->formula.get_vars()) {
            if (prep_handler.get_aut_assignment().is_co_finite(t)) {
                prep_handler.underapprox_languages();
                this->precision = LenNodePrecision::UNDERAPPROX;
                STRACE("str", tout << " - UNDERAPPROXIMATE languages\n";);
                break;
            }
        }

        prep_handler.propagate_eps();
        prep_handler.propagate_variables();
        prep_handler.generate_identities();
        prep_handler.propagate_variables();
        prep_handler.remove_trivial();
        
        // Refresh the instance
        this->formula = prep_handler.get_modified_formula();
        this->init_aut_ass = prep_handler.get_aut_assignment();
        this->init_length_sensitive_vars = prep_handler.get_len_variables();
        this->preprocessing_len_formula = prep_handler.get_len_formula();

        if(this->formula.get_predicates().size() > 0) {
            this->init_aut_ass.reduce(); // reduce all automata in the automata assignment
        }

        if(prep_handler.contains_unsat_eqs_or_diseqs()) {
            return l_false;
        }

        if (!this->init_aut_ass.is_sat()) {
            // some automaton in the assignment is empty => we won't find solution
            return l_false;
        }

        return l_undef;
    }

    bool LengthDecisionProcedure::is_suitable(const Formula &form, const AutAssignment& init_aut_ass) {
        STRACE("str", tout << "len: suitability: ";);
        for (const Predicate& pred : form.get_predicates()) {
            if(!pred.is_eq_or_ineq()) {
                STRACE("str", tout << "False - non-equation predicate\n");
                return false;
            }
        }

        // if the automata are too big --> skip the length decision procedure
        for (const auto &it : init_aut_ass) {
            if(it.second->num_of_states() > 100) {
                return false;
            }
        }

        for (const BasicTerm& t : form.get_vars()) {
            // t has language of sigma*
            if(init_aut_ass.at(t)->num_of_states() <= 1) {
                    continue;
            }

            // t is co-finite (we can underapproximate it)
            if(init_aut_ass.is_co_finite(t)) {
                continue;
            }

            // t is a literal - get shortest words
            if(init_aut_ass.is_singleton(t)) {
                continue;
            }
            STRACE("str", tout << "False - regular constraints on variable " << t << std::endl;);
            return false;
        }

        STRACE("str", tout << "True\n"; );
        return true;
    }

}