
#include "parikh_image.h"
#include "formula.h"
#include <cstdlib>

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

    LenNode ParikhImageDiseqTag::express_string_length_preceding_supposed_mismatch(const std::vector<BasicTerm>& predicate_side, size_t supposed_mismatch_pos) const {
        if (supposed_mismatch_pos == 0) {
            return LenNode(LenFormulaType::PLUS, {LenNode(0)});  // The mismatch position will be computed only based on <P, ..> tags
        }

        LenNode sum_len(LenFormulaType::PLUS);

        size_t last_term_pos_to_include = supposed_mismatch_pos - 1;
        int current_term_idx = 0;
        for (const BasicTerm& side_term : predicate_side) {
            if (current_term_idx > last_term_pos_to_include) {
                break;
            }

            ca::AtomicSymbol as = ca::AtomicSymbol::create_l_symbol(side_term); // <L,x> symbol
            sum_len.succ.push_back(LenNode(this->tag_occurence_count_vars.at(as)));
            ++current_term_idx;
        }

        return sum_len;
    }

    LenNode ParikhImageDiseqTag::count_register_stores_for_var_and_side(BasicTerm& var, char predicate_side_label) const {
        LenNode register_store_count (LenFormulaType::PLUS);
        for (const ca::AtomicSymbol& atomic_symbol : this->atomic_symbols) {
            bool is_register_store = (atomic_symbol.type == ca::AtomicSymbol::TagType::REGISTER_STORE);
            bool matches_var  = (atomic_symbol.var == var);
            bool matches_side = (atomic_symbol.label == predicate_side_label);

            if (is_register_store && matches_var && matches_side) {
                const BasicTerm& symbol_count_var = this->tag_occurence_count_vars.at(atomic_symbol);
                register_store_count.succ.push_back(LenNode(symbol_count_var));
            }
        }
        return register_store_count;
    }


    std::pair<LenNode, size_t> ParikhImageDiseqTag::express_mismatch_position(const std::vector<BasicTerm>& predicate_side, size_t mismatch_pos, size_t sample_order_label, const LenNode* offset_var) const {
        const BasicTerm& var = predicate_side[mismatch_pos];
        LenNode mismatch_pos_formula = express_string_length_preceding_supposed_mismatch(predicate_side, mismatch_pos);
        // add symbol <P, var, label_left, 0> where var is i-th variable on left side of diseq
        ca::AtomicSymbol mismatch_pos_sym = ca::AtomicSymbol::create_p_symbol(var, sample_order_label);
        auto mismatch_sym_var_it = this->tag_occurence_count_vars.find(mismatch_pos_sym);
        if (mismatch_sym_var_it == this->tag_occurence_count_vars.end()) {
            return std::make_pair(LenNode(LenFormulaType::FALSE), 0);  // The mismatch guess is not possible
        }
        size_t mismatch_term_pos = mismatch_pos_formula.succ.size();
        mismatch_pos_formula.succ.push_back(LenNode(mismatch_sym_var_it->second));

        if (offset_var != nullptr) {
            mismatch_pos_formula.succ.push_back(*offset_var);
        }

        return std::make_pair(mismatch_pos_formula, mismatch_term_pos);
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
    LenNode ParikhImageDiseqTag::get_mismatch_formula(size_t left_mismatch_pos, size_t right_mismatch_pos, const Predicate& diseq, const LenNode& rhs_offset) {
        // labels of the <P> symbols
        char label_left = 1, label_right = 2;
        BasicTerm var_left  = diseq.get_left_side()[left_mismatch_pos];
        BasicTerm var_right = diseq.get_right_side()[right_mismatch_pos];

        auto left_var_order_pos  = std::find(this->ca.var_order.begin(), this->ca.var_order.end(), var_left);
        auto right_var_order_pos = std::find(this->ca.var_order.begin(), this->ca.var_order.end(), var_right);

        // The order of observed mismatch samples given by the guess of variables might be opposite due to the structure of the automaton
        bool will_rhs_be_sampled_before_lhs = std::distance(this->ca.var_order.begin(), left_var_order_pos) > std::distance(this->ca.var_order.begin(), right_var_order_pos);

        if (will_rhs_be_sampled_before_lhs) {
            label_left  = 2;
            label_right = 1;
        }

        auto [lhs_mismatch_pos_expr, lhs_mismatch_in_var_node_idx] = express_mismatch_position(diseq.get_left_side(), left_mismatch_pos, label_left);
        if (lhs_mismatch_pos_expr.type == LenFormulaType::FALSE) return lhs_mismatch_pos_expr;

        auto [rhs_mismatch_pos_expr, rhs_mismatch_in_var_node_idx] = express_mismatch_position(diseq.get_right_side(), right_mismatch_pos, label_right, &rhs_offset);
        if (rhs_mismatch_pos_expr.type == LenFormulaType::FALSE) return rhs_mismatch_pos_expr;

        LenNode lhs_register_stores_cnt = count_register_stores_for_var_and_side(var_left, label_left);
        LenNode lhs_has_register_store(LenFormulaType::LEQ, { 1, lhs_register_stores_cnt });

        LenNode rhs_register_stores_cnt = count_register_stores_for_var_and_side(var_right, label_right);
        LenNode rhs_has_register_store(LenFormulaType::LEQ, { 1, rhs_register_stores_cnt });

        // If left_var == right_var, we don't know which sample will be seen first - create a disjunction for both branches
        if (var_right == var_left) {
            // Right now we have:
            // lhs_mismatch_pos = <L, x> + ... <L, z> + <P, var, 1>
            // rhs_mismatch_pos = <L, x> + ... <L, z> + <P, var, 2>

            LenNode mismatch_position_case_split(LenFormulaType::OR);

            // (lhs < rhs) lhs sees mismatch sooner than rhs
            {
                LenNode rhs_sees_mismatch_later = rhs_mismatch_pos_expr;
                rhs_sees_mismatch_later.succ.push_back(lhs_mismatch_pos_expr.succ[lhs_mismatch_in_var_node_idx]);  // <L, x> + ... <L, z> + <P, var, 2> + <P, var, 1>

                LenNode branch(LenFormulaType::EQ, {lhs_mismatch_pos_expr, rhs_sees_mismatch_later});
                mismatch_position_case_split.succ.push_back(branch);
            }

            // (lhs > rhs) rhs sees mismatch sooner than lhs
            {
                LenNode lhs_sees_mismatch_later = lhs_mismatch_pos_expr;
                lhs_sees_mismatch_later.succ.push_back(rhs_mismatch_pos_expr.succ[rhs_mismatch_in_var_node_idx]); // <L, x> + ... <L, z> + <P, var, 1> + <P, var, 2>

                LenNode rhs_sees_mismatch_sooner = rhs_mismatch_pos_expr;
                rhs_mismatch_pos_expr.succ[rhs_mismatch_in_var_node_idx] = lhs_mismatch_pos_expr.succ[lhs_mismatch_in_var_node_idx]; // Replace the trailing <P, var, 2> with <P, var, 1>

                LenNode branch(LenFormulaType::EQ, {lhs_sees_mismatch_later, rhs_sees_mismatch_sooner});
                mismatch_position_case_split.succ.push_back(branch);
            }

            return LenNode(LenFormulaType::AND, {
                mismatch_position_case_split,
                lhs_has_register_store,
                rhs_has_register_store
            });
        }

        // #Note(mhecko): These two top-level conjuncts should be redundant - the automaton structure should force
        //                seeing at least one <P, x, 1> and <P, x, 2> symbols. Therefore, it should not be
        //                necessary to prevent from trivial solutions 0=0.
        // LenNode some_lhs_mismatch_seen(LenFormulaType::LEQ, { 1, LenNode(first_mismatch_sym_var_it->second) });
        // LenNode some_rhs_mismatch_seen(LenFormulaType::LEQ, { 1, LenNode(second_mismatch_sym_var_it->second) });

        LenNode mismatch_position_is_same(LenFormulaType::EQ, { lhs_mismatch_pos_expr, rhs_mismatch_pos_expr});

        return LenNode(LenFormulaType::AND, {
            mismatch_position_is_same,
            lhs_has_register_store,
            rhs_has_register_store
        });

    }

    LenNode ParikhImageDiseqTag::ensure_symbol_uniqueness_using_total_sum(std::map<mata::Symbol, std::vector<LenNode>>& symbol_to_register_sample_vars) const {
        LenNode resulting_conjunction(LenFormulaType::AND);
        resulting_conjunction.succ.reserve(symbol_to_register_sample_vars.size());

        for (auto& [symbol, transitions_sampling_symbol] : symbol_to_register_sample_vars) {
            if (util::is_dummy_symbol(symbol)) {
                // Dummy symbols stand for any symbol not present in the formula and two samples of these symbols are considered as different
                continue;
            }

            LenNode total_sum(LenFormulaType::PLUS, transitions_sampling_symbol);
            LenNode total_sum_bound(LenFormulaType::LEQ, {total_sum, 1}); // I.e., there cannot be more than two 'a's sampled - the samples would be equal
            resulting_conjunction.succ.push_back(total_sum_bound);
        }

        if (resulting_conjunction.succ.empty()) {
            return LenNode(LenFormulaType::TRUE);
        }

        return resulting_conjunction;
    }

    LenNode ParikhImageDiseqTag::ensure_symbol_uniqueness_using_implication(std::map<mata::Symbol, std::vector<LenNode>>& symbol_to_register_sample_vars) const {
        LenNode resulting_conjunction(LenFormulaType::AND);
        for (const ca::AtomicSymbol& ats : this->atomic_symbols) {
            if (ats.type == ca::AtomicSymbol::TagType::REGISTER_STORE) { // symbol is of the form <R,a,l>
                // the dummy symbol represents all other symbols --> we don't generate the diff
                // symbol formula as these symbols are not equal. The only case we consider is that the symbol belongs to the same variable.
                // In that case we generate the #<R,x,a,1> >= 1 -> #<R,x,a,2> = 0
                std::vector<LenNode> register_store_vars_writing_same_symbol = symbol_to_register_sample_vars[ats.symbol];
                if (util::is_dummy_symbol(ats.symbol)) {
                    register_store_vars_writing_same_symbol = { ats.var };
                }

                LenNode sum(LenFormulaType::PLUS);
                for (const LenNode& var_node : register_store_vars_writing_same_symbol) {
                    // Check whether the same alphabet symbol, e.g., 'a' can be sampled also on the other side
                    ca::AtomicSymbol counterpart = ca::AtomicSymbol::create_r_symbol(var_node.atom_val, (ats.label == 1 ? char(2) : char(1)), ats.symbol);

                    auto iter = this->tag_occurence_count_vars.find(counterpart);
                    // if there is not the counterpart, we don't have to generate the formula
                    if (iter == this->tag_occurence_count_vars.end()) {
                        continue;
                    }
                    sum.succ.push_back(LenNode(iter->second));
                }

                BasicTerm atsVar = this->tag_occurence_count_vars.at(ats);
                resulting_conjunction.succ.push_back(LenNode(LenFormulaType::OR, {
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

        return resulting_conjunction;
    }

    std::map<mata::Symbol, std::vector<LenNode>> ParikhImageDiseqTag::group_sampling_transition_vars_by_symbol() const {
        std::map<mata::Symbol, std::vector<LenNode>> sampling_transition_vars_by_symbol {};

        std::map<Transition, BasicTerm> transition_vars = this->get_trans_vars();

        for (const auto& [transition, transition_var] : transition_vars) {
            mata::Symbol transition_symbol = std::get<1>(transition);

            const std::set<ca::AtomicSymbol>& transition_label = this->ca.alph.get_symbol(transition_symbol);

            for (const ca::AtomicSymbol& symbol_labeling_transition: transition_label) {
                if (symbol_labeling_transition.type != ca::AtomicSymbol::TagType::REGISTER_STORE) continue;

                sampling_transition_vars_by_symbol[symbol_labeling_transition.symbol].push_back(transition_var);
            }
        }

        return sampling_transition_vars_by_symbol;
    };

    /**
     * @brief Get formula describing that <R> symbols are different on the run.
     * diff := AND(#<R,x,a,1> >= 1 -> #<R,y_1,a_1,2> + ... + #<R,y_n,a_m,2> = 0 for each a_i, y_j)
     *
     * @return LenNode diff
     */
    LenNode ParikhImageDiseqTag::get_diff_symbol_formula() {
        std::map<mata::Symbol, std::vector<LenNode>> sampling_transition_vars_by_symbol = this->group_sampling_transition_vars_by_symbol();
        LenNode resulting_formula = ensure_symbol_uniqueness_using_total_sum(sampling_transition_vars_by_symbol);
        return resulting_formula;
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
        LenNode rhs_longer_than_lhs =  LenNode(LenFormulaType::LT, {len_diff_node, LenNode(this->offset_var)});

        return rhs_longer_than_lhs;
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

    LenNode ParikhImageNotContTag::existentially_quantify_all_parikh_vars(LenNode& formula) {
        for (auto& [transition, transition_var] : this->get_trans_vars()) {
            formula = LenNode(LenFormulaType::EXISTS,
                              {transition_var, formula});
        }

        for (auto& var : this->get_gamma_init()) {
            formula = LenNode(LenFormulaType::EXISTS,
                              {var, formula});
        }

        for (auto& var : this->get_gamma_fin()) {
            formula = LenNode(LenFormulaType::EXISTS,
                              {var, formula});
        }

        for (auto& var : this->get_sigma()) {
            formula = LenNode(LenFormulaType::EXISTS,
                              {var, formula});
        }

        return formula;
    }

    LenNode ParikhImageNotContTag::get_not_cont_formula(const Predicate& not_contains) {
        LenNode top_level_parikh = compute_parikh_image();
        std::map<Transition, BasicTerm> top_level_parikh_vars = this->get_trans_vars();

        // #Optimize(mhecko): We should just rename the variables found in the formula instead
        //                    of recomputing it from scratch.

        LenNode second_level_parikh = compute_parikh_image(); // We don't want to recompute length vars |x|, |y|, etc.
        std::map<Transition, BasicTerm> second_level_parikh_vars = this->get_trans_vars();

        STRACE("str-not-contains", tout << "* Parikh image symbols:  " << std::endl;
            for(const auto& [sym, bt] : this->tag_occurence_count_vars) {
                tout << bt.to_string() << " : " << sym.to_string() << std::endl;
            }
            tout << std::endl;
        );
        STRACE("str-not-contains", tout << "* compute_parikh_image:  " << std::endl << top_level_parikh << std::endl << std::endl;);

        LenNode rhs_with_offset_longer_than_lhs = mk_rhs_longer_than_lhs_formula(not_contains);
        STRACE("str-not-contains", tout << "* rhs+offset is longer than lhs:  :  " << std::endl << rhs_with_offset_longer_than_lhs << std::endl << std::endl;);

        LenNode mismatch = get_nt_all_mismatch_formula(not_contains);
        STRACE("str-not-contains", tout << "* get_mismatch_formula:  " << std::endl << mismatch << std::endl << std::endl;);

        LenNode var_lengths_from_tag_count_formula = get_var_length(not_contains.get_set());
        STRACE("str-not-contains", tout << "* get_var_length:  " << std::endl << var_lengths_from_tag_count_formula << std::endl << std::endl;);

        LenNode diff_symbol = get_diff_symbol_formula();
        STRACE("str-not-contains", tout << "* get_diff_symbol_formula:  " << std::endl << diff_symbol << std::endl << std::endl;);

        LenNode parikh_images_agree = mk_parikh_images_encode_same_word_formula(top_level_parikh_vars, second_level_parikh_vars);

        LenNode parikh_contains_conflict_for_offset(
            LenFormulaType::OR, {
            rhs_with_offset_longer_than_lhs,
            LenNode(LenFormulaType::AND, {
                mismatch,
                diff_symbol
            })}
        );

        LenNode log_true(LenFormulaType::TRUE, {});
        LenNode exist_alternative_parikh_with_conflict(
            LenFormulaType::AND, {
                second_level_parikh,
                parikh_images_agree,
                parikh_contains_conflict_for_offset
            }
        );
        exist_alternative_parikh_with_conflict = existentially_quantify_all_parikh_vars(exist_alternative_parikh_with_conflict);

        LenNode formula = LenNode(LenFormulaType::AND, {
            top_level_parikh,
            var_lengths_from_tag_count_formula,
            LenNode(LenFormulaType::FORALL, {
                this->offset_var,
                LenNode( // K >= 0 -> conflict must exists
                    LenFormulaType::OR,
                    {
                        LenNode(LenFormulaType::LT, {LenNode(this->offset_var), 0}),
                        exist_alternative_parikh_with_conflict
                    }
                )
            }),
        });

        STRACE("str-not-contains", tout << "* resulting_formula:  " << std::endl << formula << std::endl << std::endl;);

        { // Debug
            const char* out_file_path = std::getenv("NOODLER_NC_WRITE_LIA_INTO");
            if (out_file_path != nullptr) {
                std::ofstream output_file(out_file_path);
                if (output_file.is_open()) {
                    write_len_formula_as_smt2(formula, output_file);
                    output_file.close();
                }
            }
        }

        return formula;
    }

    LenNode ParikhImageNotContTag::get_offset_var() const {
        return this->offset_var;
    }
}