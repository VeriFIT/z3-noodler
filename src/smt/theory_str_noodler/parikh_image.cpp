
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
     * @brief Compute Parikh image with the free variables containing values of registers. 
     * Assumes that each register is set in each symbol of the CA alphabet.
     * 
     * phi_reg := (conj r = (sum #t * a_r for each t \in Delta) for each register r)
     * phi_parikh := phi_parikh(nfa) && phi_reg
     * 
     * @return LenNode phi_parikh
     */
    LenNode ParikhImageCA::compute_parikh_image() {
        this->reg_var.clear();
        // pi is of the form of AND
        LenNode pi = ParikhImage::compute_parikh_image();
        const std::map<Transition, BasicTerm>& trans_vars = this->get_trans_vars();

        std::vector<LenNode> sum_reg {};
        // create fresh variable for each regiser
        for(size_t i = 0; i < this->ca.registers; i++) {
            this->reg_var.push_back(util::mk_noodler_var_fresh("reg"));
            sum_reg.push_back(LenNode(LenFormulaType::PLUS));
        }

        LenNode phi_reg(LenFormulaType::AND);
        for(const auto& [trans, var] : trans_vars) {
            auto symb = this->ca.alph.get_symbol(std::get<1>(trans));
            for(size_t i = 0; i < this->ca.registers; i++) {
                sum_reg[i].succ.push_back(LenNode(LenFormulaType::TIMES, {
                    var,
                    symb[i]
                }));
            }
        }
        for(size_t i = 0; i < this->ca.registers; i++) {
            if(sum_reg[i].succ.size() > 0) {
                phi_reg.succ.push_back(LenNode(LenFormulaType::EQ, {
                    this->reg_var[i],
                    sum_reg[i]
                }));
            }
        }

        return LenNode(LenFormulaType::AND, {
            pi,
            phi_reg
        });
    }


}