
#include "parikh_image.h"

namespace smt::noodler::parikh {

    /**
     * @brief Compute formula phi_init saying there is one initial state of a run. 
     * 
     * phi_1 := 0 <= gamma_q^I <= 1 for each q \in I 
     * phi_2 := gamma_q^I = 0 for each q \notin I
     * phi_3 := 1 = gamma_q^I + gamma_q^I + ... for each q \in I (exactly one initial state is selected)
     * phi_init = phi_1 && phi_2 && phi_3
     * 
     * @return LenNode phi_init
     */
    LenNode ParikhImage::compute_phi_init() {
        LenNode phi_init(LenFormulaType::AND);
        LenNode sum(LenFormulaType::PLUS);
        for(size_t state = 0; state < this->nfa.num_of_states(); state++) {
            // create fresh vars
            this->gamma_init.push_back(util::mk_noodler_var_fresh("gamma_init"));
            if(this->nfa.initial.contains(state)) {
                // 0 <= gamma_init[state] <= 1
                sum.succ.emplace_back(gamma_init[state]);
                phi_init.succ.emplace_back( LenNode(LenFormulaType::AND, {
                    LenNode(LenFormulaType::LEQ, {0, this->gamma_init[state]}),
                    LenNode(LenFormulaType::LEQ, {this->gamma_init[state], 1})
                }) );
            } else {
                // gamma_init[state] == 0
                phi_init.succ.emplace_back( LenNode(LenFormulaType::EQ, {0, this->gamma_init[state]}) );
            }
        }
        // sum gamma_init[state] for state is initial == 1
        // exactly one initial state is selected
        phi_init.succ.emplace_back( LenNode(LenFormulaType::EQ, {sum, 1}) );
        return phi_init;
    }

    /**
     * @brief Compute formula phi_fin saying there might be a final state as the last state of a run.
     * 
     * phi_1 := 0 <= gamma_q^F <= 1 for each q \in F
     * phi_2 := gamma_q^F = 0 for each q \notin F
     * phi_fin = phi_1 && phi_2
     * 
     * @return LenNode phi_fin 
     */
    LenNode ParikhImage::compute_phi_fin() {
         // phi_fin
        LenNode phi_fin(LenFormulaType::AND);
        for(size_t state = 0; state < this->nfa.num_of_states(); state++) {
            // create fresh vars
            this->gamma_fin.push_back(util::mk_noodler_var_fresh("gamma_fin"));
            if(this->nfa.final.contains(state)) {
                // 0 <= gamma_fin[state] <= 1
                phi_fin.succ.emplace_back( LenNode(LenFormulaType::AND, {
                    LenNode(LenFormulaType::LEQ, {0, this->gamma_init[state]}),
                    LenNode(LenFormulaType::LEQ, {this->gamma_init[state], 1})
                }) );
            } else {
                // gamma_fin[state] == 0
                phi_fin.succ.emplace_back( LenNode(LenFormulaType::EQ, {0, this->gamma_fin[state]}) );
            }
        }
        return phi_fin;
    }

    /**
     * @brief Compute formula phi_kirch ensuring that on a run the number of times we enter the state 
     * equals the number of states we leave the state (+/- one when the state is the first one or the last one).
     * 
     * phi_q := gamma_q^I + ( sum #t for each t = (.,.,q) \in \Delta ) = gamma_q^F + ( sum #t for each t = (q,.,.) \in \Delta )
     * phi_kirch := conj phi_q for each q \in Q
     * 
     * @param succ_trans [q] = [(q,.,.), .... ]. Vector (idexed by states q) containing list of transitions with the source state being q  
     * @param prev_trans [q] = [(.,.,q), .... ]. Vector (idexed by states q) containing list of transitions with the target state being q 
     * @return LenNode phi_kirch
     */
    LenNode ParikhImage::compute_phi_kirch(const TransitionCol& succ_trans, const TransitionCol& prev_trans) {
        LenNode phi_kirch(LenFormulaType::AND);

        for (size_t state = 0; state < this->nfa.num_of_states(); state++) {
            LenNode sum_succ(LenFormulaType::PLUS);
            LenNode sum_prev(LenFormulaType::PLUS);

            for(const Transition& tr : succ_trans[state]) {
                sum_succ.succ.push_back(this->trans.at(tr));
            }
            sum_succ.succ.push_back(this->gamma_fin[state]);

            for(const Transition& tr : prev_trans[state]) {
                sum_prev.succ.push_back(this->trans.at(tr));
            }
            sum_prev.succ.push_back(this->gamma_init[state]);
            phi_kirch.succ.push_back(LenNode(LenFormulaType::EQ, {
                sum_prev,
                sum_succ
            }));
        }
        return phi_kirch;
    }

    /**
     * @brief Compute formulae phi_span ensures connectedness of a run. Formula checks if there is a consistent 
     * spanning tree wrt a run. 
     * 
     * phi^1_q := sigma_q = 0 <=> gamma^I_q = 1 (the first state has distance 1)
     * phi^2_q := sigma_q = -1 => (gamma^I_q = 0 && (conj #t = 0 for each t = (.,.,q)) ) (if a state does not occurr on the
     *      run, #t of transitions leading to this state is zero)
     * phi^3_q := sigma_q > 0 => (disj #t > 0 && sigma_r >= 0 && sigma_q = sigma_r + 1 for each t = (r,.,q)) 
     *      (if a state q occurs on the run and it is not initial, there is some predecessor of this state in the run with 
     *      the smaller distance ).
     * phi_span = (conj phi^1_q && phi^2_q && phi^3_q for each state q)
     * 
     * @param succ_trans [q] = [(q,.,.), .... ]. Vector (idexed by states q) containing list of transitions with the source state being q 
     * @param prev_trans [q] = [(.,.,q), .... ]. Vector (idexed by states q) containing list of transitions with the target state being q 
     * @return LenNode phi_span 
     */
    LenNode ParikhImage::compute_phi_span(const TransitionCol& succ_trans, const TransitionCol& prev_trans) {
       LenNode phi_span(LenFormulaType::AND);

        for (size_t state = 0; state < this->nfa.num_of_states(); state++) {
            this->sigma.push_back(util::mk_noodler_var_fresh("sigma"));

            LenNode cl1(LenFormulaType::AND, {
                LenNode(LenFormulaType::OR, {
                    LenNode(LenFormulaType::NEQ, {this->sigma[state], 0}),
                    LenNode(LenFormulaType::EQ, {this->gamma_init[state], 1}),
                }),
                LenNode(LenFormulaType::OR, {
                    LenNode(LenFormulaType::EQ, {this->sigma[state], 0}),
                    LenNode(LenFormulaType::NEQ, {this->gamma_init[state], 1}),
                }),
            });

            LenNode conj_prev(LenFormulaType::AND);
            for(const Transition& tr : prev_trans[state]) {
                conj_prev.succ.push_back(LenNode(LenFormulaType::EQ, {
                    this->trans.at(tr),
                    0
                }));
            }
            LenNode cl2(LenFormulaType::OR, {
                LenNode(LenFormulaType::NEQ, { this->sigma[state], -1 }),
                LenNode(LenFormulaType::AND, {
                    LenNode(LenFormulaType::EQ, { this->gamma_init[state], 0 }),
                    conj_prev,
                })
            });

            LenNode disj_prev(LenFormulaType::OR);
            for(const Transition& tr : prev_trans[state]) {
                disj_prev.succ.push_back(LenNode(LenFormulaType::AND, {
                    LenNode(LenFormulaType::LT, {0, this->trans.at(tr)}),
                    LenNode(LenFormulaType::LEQ, {0, this->sigma[std::get<0>(tr)]}),
                    LenNode(LenFormulaType::EQ, {
                        this->sigma[state],
                        LenNode(LenFormulaType::PLUS, { this->sigma[std::get<0>(tr)], 1 }),
                    })
                }));
            }
            LenNode cl3(LenFormulaType::OR, {
                LenNode(LenFormulaType::LEQ, {this->sigma[state], 0}),
                disj_prev
            });

            phi_span.succ.push_back(LenNode(LenFormulaType::AND, {
                cl1,
                cl2,
                cl3
            }));
        }
        return phi_span;
    }

    LenNode ParikhImage::compute_parikh_image() {
        this->gamma_init.clear();
        this->gamma_fin.clear();
        this->sigma.clear();
        this->trans.clear();

        LenNode phi_trans(LenFormulaType::AND);
        TransitionCol succ_trans(nfa.num_of_states());
        TransitionCol prev_trans(nfa.num_of_states());
        for(const auto& tr : nfa.delta.transitions()) {
            Transition tr_inst = {tr.source, tr.symbol, tr.target}; 
            trans.insert({tr_inst, util::mk_noodler_var_fresh("trans")});
            succ_trans[tr.source].push_back(tr_inst);
            prev_trans[tr.target].push_back(tr_inst);
            phi_trans.succ.push_back(LenNode(LenFormulaType::LEQ, {0, trans.at(tr_inst)}));
        }

        LenNode phi_init = compute_phi_init();
        LenNode phi_fin = compute_phi_fin();
        LenNode phi_kirch = compute_phi_kirch(succ_trans, prev_trans);
        LenNode phi_span = compute_phi_span(succ_trans, prev_trans);

        return LenNode(LenFormulaType::AND, {
            phi_init,
            phi_fin,
            phi_trans,
            phi_kirch,
            phi_span
        });
    }

    /**
     * @brief Get the formula describing |L| != |R| where L != R is @p diseq.
     * For x_1 ... x_n != y_1 ... x_m create
     * phi := #<L,x_1> + ... + #<L,x_n> != #<L,y_1> + ... + #<L,y_m>
     * 
     * @param diseq Disequation L != R
     * @return LenNode phi
     */
    LenNode ParikhImageCA::get_diseq_length(const Predicate& diseq) {
        // e.g., for x.y get var_{r_x} + var_{r_y} where r_x is the CA register corresponding to the string variable x and 
        // var_r is int variable describing value of register r after the run.
        auto concat_len = [&](const Concat& con) -> LenNode {
            LenNode sum_len(LenFormulaType::PLUS);
            for(const BasicTerm& bt : con) {
                ca::AtomicSymbol as = {0, bt, 0, 0}; // <L,x> symbol
                sum_len.succ.push_back(LenNode(LenFormulaType::LEAF, { this->symbol_var.at(as) }));
            }
            return sum_len;
        };

        return LenNode(LenFormulaType::NEQ, {
            concat_len(diseq.get_left_side()), 
            concat_len(diseq.get_right_side())
        });
    }


    LenNode ParikhImageCA::get_all_mismatch_formula(const Predicate& diseq) {
        // create formula OR( mismatch(i,j) where i is position of left of diseq and j is position of right of diseq )
        LenNode mismatch(LenFormulaType::OR);
        for(size_t i = 0; i < diseq.get_left_side().size(); i++) {
            for (size_t j = 0; j < diseq.get_right_side().size(); j++) {
                mismatch.succ.push_back(get_mismatch_formula(i, j, diseq));
            }
        }
        return mismatch;
    }


    LenNode ParikhImageCA::get_diseq_formula(const Predicate& diseq) {
        LenNode parikh = compute_parikh_image();
        LenNode diseq_len = get_diseq_length(diseq);
        LenNode mismatch = get_all_mismatch_formula(diseq);
        
        return LenNode(LenFormulaType::AND, {
            parikh,
            LenNode(LenFormulaType::OR, {
                diseq_len,
                mismatch,
            })
        });
    }

    /**
     * @brief Construct formula counting number of AtomicSymbol in each set on the transitions.
     * For each AtomicSymbol e.q., <L,x> create a fresh variable #<L,x> and generate
     * #<L,x> = sum( #t, where transition symbol -- set of AtomicSymbol -- contains <L,x> )
     * 
     * @return LenNode AND (#symb for each AtomicSymbol symb)
     */
    LenNode ParikhImageCA::symbol_count_formula() {
        this->symbol_var.clear();
        const std::map<Transition, BasicTerm>& trans_vars = this->get_trans_vars();

        // create mapping: AtomicSymbol a -> var_a
        std::map<ca::AtomicSymbol, LenNode> sum_symb {};
        for(const ca::AtomicSymbol& as : this->atomic_symbols) {
            this->symbol_var.insert({as, util::mk_noodler_var_fresh("symb")});
            sum_symb.insert( {as, LenNode(LenFormulaType::PLUS)});
        }

        LenNode phi_cnt(LenFormulaType::AND);
        for(const auto& [trans, var] : trans_vars) {
            // set of atomic symbols
            auto symb = this->ca.alph.get_symbol(std::get<1>(trans));
            for(const ca::AtomicSymbol& as : symb) {
                sum_symb.at(as).succ.push_back(LenNode(LenFormulaType::LEAF, { var }));
            }
        }

        // generate equations var_a = #t_1 + #t_2 ... where #t_1 is variable of a 
        // transition containing in symbol set a
        for (const auto& [as, var] : this->symbol_var) {
            const LenNode& act = sum_symb.at(as);
            if(act.succ.size() > 0) {
                phi_cnt.succ.push_back(LenNode(LenFormulaType::EQ, {
                    this->symbol_var.at(as),
                    act
                }));
            }
        }

        return phi_cnt;
    }

    /**
     * @brief Get mismatch formula for particular positions @p i and @p j. 
     * For x_1 ... x_n != y_1 ... y_m create 
     * mismatch(i,j) := #<L,x_1> + ... + #<L,x_{i-1}> + #<P,x_i,0> = #<L,y_1> + ... + #<L,y_{j-1}> + #<P,y_j,1>
     * where #symb is LIA variable counting number of occurrences of the symbol symb during 
     * the run. Stored in this->symbol_var and computed by symbol_count_formula.
     * 
     * E.g., for x_1 x_2 x_3 != y_1 y_2 create a formula 
     * mismatch(3,2) := #<L,x_1> + #<L,x_2> + #<P,x_3,0> = #<L,y_1> + #<P,y_2,1>
     * 
     * 
     * @param i Position on the left side of @p diseq
     * @param j Position on the right side of @p diseq
     * @param diseq Diseq
     * @return LenNode mismatch(i,j)
     */
    LenNode ParikhImageCA::get_mismatch_formula(size_t i, size_t j, const Predicate& diseq) {
        auto concat_len = [&](const Concat& con, size_t max_ind) -> LenNode {
            LenNode sum_len(LenFormulaType::PLUS);
            size_t ind = 0;
            for(const BasicTerm& bt : con) {
                if (ind > max_ind) {
                    break;
                }
                ca::AtomicSymbol as = {0, bt, 0, 0}; // <L,x> symbol
                sum_len.succ.push_back(LenNode(LenFormulaType::LEAF, { this->symbol_var.at(as) }));
                ++ind;
            }
            return sum_len;
        };

        LenNode left = concat_len(diseq.get_left_side(), i - 1);
        // add symbol <P, var, 0, 0> where var is i-th variable on left side of diseq
        left.succ.push_back(LenNode(LenFormulaType::LEAF, { this->symbol_var.at({1, diseq.get_left_side()[i], 1, 0}) }));

        LenNode right = concat_len(diseq.get_right_side(), j-1);
        // add symbol <P, var, 1, 0> where var is j-th variable on left side of diseq
        right.succ.push_back(LenNode(LenFormulaType::LEAF, { this->symbol_var.at({1, diseq.get_right_side()[j], 2, 0}) }));

        return LenNode(LenFormulaType::EQ, {
            left,
            right
        });
    }

}