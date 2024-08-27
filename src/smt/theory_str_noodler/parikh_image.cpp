
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
    LenNode ParikhImage::compute_phi_kirch(const TransitionStateVector& succ_trans, const TransitionStateVector& prev_trans) {
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
    LenNode ParikhImage::compute_phi_span(const TransitionStateVector& succ_trans, const TransitionStateVector& prev_trans) {
       LenNode phi_span(LenFormulaType::AND);

        for (size_t state = 0; state < this->nfa.num_of_states(); state++) {
            this->sigma.push_back(util::mk_noodler_var_fresh("sigma"));
        }

        for (size_t state = 0; state < this->nfa.num_of_states(); state++) {
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
        TransitionStateVector succ_trans(nfa.num_of_states());
        TransitionStateVector prev_trans(nfa.num_of_states());
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

        STRACE("str-diseq", tout << "* Parikh image transitions:  " << std::endl;
            for(const auto& [tr, bt] : this->trans) {
                tout << bt.to_string() << " : " << std::get<0>(tr) << " -(" << std::get<1>(tr) << ")-> " << std::get<2>(tr) << std::endl;
            }
            tout << std::endl;
        );

        return LenNode(LenFormulaType::AND, {
            phi_init,
            phi_fin,
            phi_trans,
            phi_kirch,
            phi_span
        });
    }


    void ParikhImage::print_transition_var_labeling(std::ostream& output_stream) const {
        for (const auto& [transition, transition_var] : this->trans) {
            output_stream << "(" << std::get<0>(transition) << ", "
                          << std::get<1>(transition) << ", "
                          << std::get<2>(transition) << ") <-> "
                          << transition_var << std::endl;
        }
    }

    /**
     * @brief Get the formula describing |L| != |R| where L != R is @p diseq.
     * For x_1 ... x_n != y_1 ... x_m create
     * phi := #<L,x_1> + ... + #<L,x_n> != #<L,y_1> + ... + #<L,y_m>
     *
     * @param diseq Disequation L != R
     * @return LenNode phi
     */
    LenNode ParikhImageDiseqTag::get_diseq_length(const Predicate& diseq) {
        // e.g., for x.y get var_{r_x} + var_{r_y} where r_x is the TagAut register corresponding to the string variable x and
        // var_r is int variable describing value of register r after the run.
        auto concat_len = [&](const Concat& con) -> LenNode {
            LenNode sum_len(LenFormulaType::PLUS);
            for(const BasicTerm& bt : con) {
                ca::AtomicSymbol as = ca::AtomicSymbol::create_l_symbol(bt); // <L,x> symbol
                if(this->tag_occurence_count_vars.contains(as)) {
                    sum_len.succ.push_back(LenNode(this->tag_occurence_count_vars.at(as)));
                }
            }
            return sum_len;
        };

        return LenNode(LenFormulaType::NEQ, {
            concat_len(diseq.get_left_side()),
            concat_len(diseq.get_right_side())
        });
    }

    LenNode ParikhImageDiseqTag::get_var_length(const std::set<BasicTerm>& vars) {
        LenNode lengths(LenFormulaType::AND);
        // for each variable generate |x| = #<L,x>
        for(const BasicTerm& bt : vars) {
            ca::AtomicSymbol as = ca::AtomicSymbol::create_l_symbol(bt); // <L,x> symbol
            // if the symbol is completely missing in the automaton, we say FALSE
            if(!this->tag_occurence_count_vars.contains(as)) {
                lengths.succ.push_back(LenNode(LenFormulaType::FALSE));
            } else {
                lengths.succ.push_back(LenNode(LenFormulaType::EQ, {
                    LenNode(this->tag_occurence_count_vars.at(as)),
                    LenNode(bt),
                }));
            }
        }
        return lengths;
    }



    LenNode ParikhImageDiseqTag::get_all_mismatch_formula(const Predicate& diseq) {
        // create formula OR( mismatch(i,j) where i is position of left of diseq and j is position of right of diseq )
        LenNode mismatch(LenFormulaType::OR);
        for(size_t i = 0; i < diseq.get_left_side().size(); i++) {
            for (size_t j = 0; j < diseq.get_right_side().size(); j++) {
                mismatch.succ.push_back(get_mismatch_formula(i, j, diseq));
            }
        }
        return mismatch;
    }


    LenNode ParikhImageDiseqTag::get_diseq_formula(const Predicate& diseq) {
        LenNode parikh = compute_parikh_image();

        STRACE("str-diseq", tout << "* Parikh image symbols:  " << std::endl;
            for(const auto& [sym, bt] : this->tag_occurence_count_vars) {
                tout << bt.to_string() << " : " << sym.to_string() << std::endl;
            }
            tout << std::endl;
        );
        STRACE("str-diseq", tout << "* compute_parikh_image:  " << std::endl << parikh << std::endl << std::endl;);
        LenNode diseq_len = get_diseq_length(diseq);
        STRACE("str-diseq", tout << "* get_diseq_length:  " << std::endl << diseq_len << std::endl << std::endl;);
        LenNode mismatch = get_all_mismatch_formula(diseq);
        STRACE("str-diseq", tout << "* get_mismatch_formula:  " << std::endl << mismatch << std::endl << std::endl;);
        LenNode len = get_var_length(diseq.get_set());
        STRACE("str-diseq", tout << "* get_var_length:  " << std::endl << len << std::endl << std::endl;);
        LenNode diff_symbol = get_diff_symbol_formula();
        STRACE("str-diseq", tout << "* get_diff_symbol_formula:  " << std::endl << diff_symbol << std::endl << std::endl;);

        return LenNode(LenFormulaType::AND, {
            parikh,
            len,
            LenNode(LenFormulaType::OR, {
                diseq_len,
                LenNode(LenFormulaType::AND, {
                    mismatch,
                    diff_symbol
                })
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
    LenNode ParikhImageDiseqTag::symbol_count_formula() {
        this->tag_occurence_count_vars.clear();
        const std::map<Transition, BasicTerm>& trans_vars = this->get_trans_vars();

        // create mapping: AtomicSymbol a -> var_a
        std::map<ca::AtomicSymbol, LenNode> sum_symb {};
        for(const ca::AtomicSymbol& as : this->atomic_symbols) {
            this->tag_occurence_count_vars.insert({as, util::mk_noodler_var_fresh("symb")});
            sum_symb.insert( {as, LenNode(LenFormulaType::PLUS)});
        }

        LenNode phi_cnt(LenFormulaType::AND);
        for(const auto& [trans, var] : trans_vars) {
            // set of atomic symbols
            auto symb = this->ca.alph.get_symbol(std::get<1>(trans));
            for(const ca::AtomicSymbol& as : symb) {
                sum_symb.at(as).succ.emplace_back(LenNode(var));
            }
        }

        // generate equations var_a = #t_1 + #t_2 ... where #t_1 is variable of a
        // transition containing in symbol set a
        for (const auto& [as, var] : this->tag_occurence_count_vars) {
            const LenNode& act = sum_symb.at(as);
            if(act.succ.size() > 0) {
                phi_cnt.succ.push_back(LenNode(LenFormulaType::EQ, {
                    this->tag_occurence_count_vars.at(as),
                    act
                }));
            }
        }

        return phi_cnt;
    }

    /**
     * @brief Get mismatch formula for particular positions @p i and @p j.
     * For x_1 ... x_n != y_1 ... y_m create
     * mismatch(i,j) := #<L,x_1> + ... + #<L,x_{i-1}> + #<P,x_i,lab_left> = #<L,y_1> + ... + #<L,y_{j-1}> + #<P,y_j,lab_right> && #<P,x_i,0> >= 1 && #<P,y_j,1> >= 1
     * where #symb is LIA variable counting number of occurrences of the symbol symb during
     * the run. Stored in this->symbol_var and computed by symbol_count_formula and
     * lab_left = 1 && lab_right = 2 <-> x_i > y_j (and vice versa)
     *
     * Moreover if x_i = y_j, we need to add #<P,y_j,1> to the right hand side formula.
     *
     * We also need to be sure that the mismatch symbols were properly selected:
     * rmatch_left := #<R,x_i,lab_left,a1> + ... +  #<R,x_i,lab_left,an> >= 1
     * rmatch_right := #<R,y_j,lab_right,a1> + ... +  #<R,y_j,lab_right,an> >= 1
     * rmatch := rmatch_left + rmatch_right
     *
     * @param i Position on the left side of @p diseq
     * @param j Position on the right side of @p diseq
     * @param diseq Diseq
     * @param add_right term that should be added to the right side
     * @return LenNode mismatch(i,j) && rmatch
     */
    LenNode ParikhImageDiseqTag::get_mismatch_formula(size_t i, size_t j, const Predicate& diseq, const LenNode& add_right) {
        auto concat_len = [&](const Concat& con, int max_ind) -> LenNode {
            LenNode sum_len(LenFormulaType::PLUS);
            int ind = 0;
            for(const BasicTerm& bt : con) {
                if (ind > max_ind) {
                    break;
                }
                ca::AtomicSymbol as = ca::AtomicSymbol::create_l_symbol(bt); // <L,x> symbol
                sum_len.succ.push_back(LenNode(this->tag_occurence_count_vars.at(as)));
                ++ind;
            }
            return sum_len;
        };
        // for x, lab generate #<R,x,lab,a_1> + ... + #<R,x,lab,a_n> for all possible a_i
        auto sum_r_symb = [&](const BasicTerm & bt, char label) -> LenNode {
            LenNode sum_r(LenFormulaType::PLUS);
            for(const ca::AtomicSymbol& ats : this->atomic_symbols) {
                if (ats.type == ca::AtomicSymbol::TagType::REGISTER_STORE && ats.var == bt && ats.label == label) {
                    sum_r.succ.push_back(LenNode(this->tag_occurence_count_vars.at(ats)));
                }
            }
            return sum_r;
        };

        // labels of the <P> symbols
        char label_left = 1, label_right = 2;
        BasicTerm var_left = diseq.get_left_side()[i];
        BasicTerm var_right = diseq.get_right_side()[j];
        if(std::distance(this->ca.var_order.begin(), std::find(this->ca.var_order.begin(), this->ca.var_order.end(), var_left)) > std::distance(this->ca.var_order.begin(), std::find(this->ca.var_order.begin(), this->ca.var_order.end(), var_right))) {
            label_left = 2;
            label_right = 1;
        }

        LenNode left = concat_len(diseq.get_left_side(), i - 1);
        // add symbol <P, var, label_left, 0> where var is i-th variable on left side of diseq
        ca::AtomicSymbol lats = ca::AtomicSymbol::create_p_symbol(var_left, label_left);
        if(!this->tag_occurence_count_vars.contains(lats)) {
            return LenNode(LenFormulaType::FALSE);
        }
        left.succ.push_back(LenNode(this->tag_occurence_count_vars.at(lats)));

        LenNode right = concat_len(diseq.get_right_side(), j-1);
        // add the add_right parameter ( 0 by default )
        right.succ.insert(right.succ.begin(), add_right);
        // add symbol <P, var, label_right, 0> where var is j-th variable on right side of diseq
        ca::AtomicSymbol rats2 = ca::AtomicSymbol::create_p_symbol(var_right, label_right);
        if(!this->tag_occurence_count_vars.contains(rats2)) {
            return LenNode(LenFormulaType::FALSE);
        }
        right.succ.push_back(LenNode(this->tag_occurence_count_vars.at(rats2)));
        // if x == y, we add #<P,x,1> to #<P,x,2>
        if (var_right == var_left) {
            ca::AtomicSymbol rats1 = ca::AtomicSymbol::create_p_symbol(var_right, 1);
            right.succ.push_back(LenNode(this->tag_occurence_count_vars.at(rats1)));
        }

        LenNode rleft(LenFormulaType::LEQ, {
            1,
            sum_r_symb(var_left, label_left)
        });
        LenNode rright(LenFormulaType::LEQ, {
            1,
            sum_r_symb(var_right, label_right)
        });

        // we need to assure that there is at least one selection of lats and rats.
        // we want to avoid trivial satisfiability 0 = 0
        return LenNode(LenFormulaType::AND, {
            LenNode(LenFormulaType::LEQ, {
                1,
                LenNode(this->tag_occurence_count_vars.at(lats))
            }),
            LenNode(LenFormulaType::LEQ, {
                1,
                LenNode(this->tag_occurence_count_vars.at(rats2))
            }),
            LenNode(LenFormulaType::EQ, {
                left,
                right
            }),
            rleft,
            rright
        });
    }

    /**
     * @brief Get formula describing that <R> symbols are different on the run.
     * diff := AND(#<R,x,a,1> >= 1 -> #<R,y_1,a_1,2> + ... + #<R,y_n,a_m,2> = 0 for each a_i, y_j)
     *
     * @return LenNode diff
     */
    LenNode ParikhImageDiseqTag::get_diff_symbol_formula() {
        LenNode conj(LenFormulaType::AND);
        std::set<mata::Symbol> syms {};

        std::map<mata::Symbol, std::vector<BasicTerm>> symb_vars {};
        for(const ca::AtomicSymbol& ats : this->atomic_symbols) {
            if (ats.type != ca::AtomicSymbol::TagType::REGISTER_STORE) continue;
            symb_vars[ats.symbol].push_back(ats.var);
        }

        // iterate over all atomic symbols
        for(const ca::AtomicSymbol& ats : this->atomic_symbols) {
            if (ats.type == ca::AtomicSymbol::TagType::REGISTER_STORE) { // symbol is of the form <R,a,l>
                // the dummy symbol represents all other symbols --> we don't generate the diff
                // symbol formula as these symbols are not equal. The only case we consider is that the symbol belongs to the same variable.
                // In that case we generate the #<R,x,a,1> >= 1 -> #<R,x,a,2> = 0
                Concat col = symb_vars[ats.symbol];
                if(util::is_dummy_symbol(ats.symbol)) {
                    col = { ats.var };
                }
                LenNode sum(LenFormulaType::PLUS);
                for(const BasicTerm& var : col) {
                    ca::AtomicSymbol counterpart = ca::AtomicSymbol::create_r_symbol(var, (ats.label == 1 ? char(2) : char(1)), ats.symbol);
                    auto iter = this->tag_occurence_count_vars.find(counterpart);
                    // if there is not the counterpart, we don't have to generate the formula
                    if (iter == this->tag_occurence_count_vars.end()) {
                        continue;
                    }
                    sum.succ.push_back(LenNode(iter->second));
                }
                BasicTerm atsVar = this->tag_occurence_count_vars.at(ats);
                conj.succ.push_back(LenNode(LenFormulaType::OR, {
                    LenNode(LenFormulaType::NOT, {
                        LenNode(LenFormulaType::LEQ, {
                            1,
                            LenNode(atsVar)
                        })
                    }),
                    LenNode(LenFormulaType::EQ, {
                        0,
                        sum
                    })
                }));
            }
        }

        return conj;
    }

    LenNode ParikhImageNotContTag::get_nt_all_mismatch_formula(const Predicate& not_cont) {
        LenNode mismatch(LenFormulaType::OR);
        for(size_t i = 0; i < not_cont.get_left_side().size(); i++) {
            for (size_t j = 0; j < not_cont.get_right_side().size(); j++) {
                mismatch.succ.push_back(get_mismatch_formula(i, j, not_cont, this->offset_var));
            }
        }
        return mismatch;
    }

    LenNode ParikhImageNotContTag::mk_rhs_longer_than_lhs_formula(const Predicate& not_contains) {

        std::unordered_map<BasicTerm, int> lhs_var_occurence_occurence_diff;

        for (const BasicTerm& term: not_contains.get_left_side()) {
            auto [old_map_entry, did_emplace_happen] = lhs_var_occurence_occurence_diff.emplace(term, 1);
            if (!did_emplace_happen) {
                old_map_entry->second += 1;
            }
        }

        for (const BasicTerm& term: not_contains.get_right_side()) {
            auto [old_map_entry, did_emplace_happen] = lhs_var_occurence_occurence_diff.emplace(term, -1);
            if (!did_emplace_happen) {
                old_map_entry->second -= 1;
            }
        }

        std::vector<LenNode> len_diff_expr;
        len_diff_expr.reserve(lhs_var_occurence_occurence_diff.size());  // Speculative

        // For notContains(xxxz, zx) we generate 2*|x|
        for (const auto& [var, var_occurence_diff] : lhs_var_occurence_occurence_diff) {
            len_diff_expr.push_back(LenNode(LenFormulaType::TIMES, {LenNode(var_occurence_diff), var}));
        }

        LenNode len_diff_node = LenNode(LenFormulaType::PLUS, len_diff_expr);
        return LenNode(LenFormulaType::LEQ, {len_diff_node, LenNode(this->offset_var)});
    }

    mata::nfa::State ParikhImageNotContTag::map_copy_state_into_its_origin(const mata::nfa::State state) const {
        return state % this->number_of_states_in_row;
    }

    std::unordered_map<StatePair, std::vector<LenNode>> ParikhImageNotContTag::group_isomorphic_transitions_across_copies(const std::map<Transition, BasicTerm>& parikh_image) const {
        std::unordered_map<StatePair, std::vector<LenNode>> isomorphic_transitions;

        for (auto& [transition, transition_var]: parikh_image) {
            size_t source_state = this->map_copy_state_into_its_origin(std::get<0>(transition));
            size_t target_state = this->map_copy_state_into_its_origin(std::get<2>(transition));

            StatePair state_pair = {source_state, target_state};
            std::vector<LenNode>& isomorphic_transition_vars = isomorphic_transitions[state_pair];
            isomorphic_transition_vars.push_back(transition_var);
        }

        return isomorphic_transitions;
    }

    LenNode ParikhImageNotContTag::mk_parikh_images_encode_same_word_formula(const std::map<Transition, BasicTerm>& parikh_image, const std::map<Transition, BasicTerm>& other_image) const {
        std::unordered_map<StatePair, std::vector<LenNode>> isomorphic_transitions = group_isomorphic_transitions_across_copies(parikh_image);
        std::unordered_map<StatePair, std::vector<LenNode>> other_isomorphic_transitions = group_isomorphic_transitions_across_copies(other_image);

        assert (isomorphic_transitions.size() == other_isomorphic_transitions.size()); // Sanity

        std::vector<LenNode> resulting_conjunction_atoms;

        for (auto& [state_pair, transition_vars] : isomorphic_transitions) {
            auto other_transition_vars_bucket = other_isomorphic_transitions.find(state_pair);

            assert (other_transition_vars_bucket != other_isomorphic_transitions.end());

            std::vector<LenNode>& other_transition_vars = other_transition_vars_bucket->second;

            LenNode lhs_vars = LenNode(LenFormulaType::PLUS, transition_vars);
            LenNode rhs_vars = LenNode(LenFormulaType::PLUS, other_transition_vars);
            LenNode equality = LenNode(LenFormulaType::EQ, {lhs_vars, rhs_vars});

            resulting_conjunction_atoms.push_back(equality);
        }

        return LenNode(LenFormulaType::AND, resulting_conjunction_atoms);
    }

    LenNode ParikhImageNotContTag::get_not_cont_formula(const Predicate& not_contains) {
        LenNode top_level_parikh = compute_parikh_image();
        LenNode second_level_parikh = ParikhImage::compute_parikh_image(); // We don't want to recompute length vars |x|, |y|, etc.

        STRACE("str-diseq", tout << "* Parikh image symbols:  " << std::endl;
            for(const auto& [sym, bt] : this->tag_occurence_count_vars) {
                tout << bt.to_string() << " : " << sym.to_string() << std::endl;
            }
            tout << std::endl;
        );
        STRACE("str-diseq", tout << "* compute_parikh_image:  " << std::endl << top_level_parikh << std::endl << std::endl;);

        LenNode rhs_with_offset_longer_than_lhs = mk_rhs_longer_than_lhs_formula(not_contains);
        STRACE("str-diseq", tout << "* rhs+offset is longer than lhs:  :  " << std::endl << rhs_with_offset_longer_than_lhs << std::endl << std::endl;);

        LenNode mismatch = get_nt_all_mismatch_formula(not_contains);
        STRACE("str-diseq", tout << "* get_mismatch_formula:  " << std::endl << mismatch << std::endl << std::endl;);

        LenNode var_lengths_from_tag_count_formula = get_var_length(not_contains.get_set());
        STRACE("str-diseq", tout << "* get_var_length:  " << std::endl << var_lengths_from_tag_count_formula << std::endl << std::endl;);

        LenNode diff_symbol = get_diff_symbol_formula();
        STRACE("str-diseq", tout << "* get_diff_symbol_formula:  " << std::endl << diff_symbol << std::endl << std::endl;);

        LenNode formula = LenNode(LenFormulaType::AND, {
            top_level_parikh,
            var_lengths_from_tag_count_formula,
            LenNode(LenFormulaType::FORALL, {
                this->offset_var,
                LenNode(LenFormulaType::OR, {
                    rhs_with_offset_longer_than_lhs,
                    LenNode(LenFormulaType::AND, {
                        mismatch,
                        diff_symbol
                    })
                })
            }),
        });

        return LenNode(LenFormulaType::FORALL, {this->offset_var, formula});
    }
}