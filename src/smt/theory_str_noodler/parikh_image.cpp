
#include "parikh_image.h"
#include "formula.h"
#include <cstdlib>

using namespace smt::noodler::ca;

namespace std {
    std::ostream& operator<<(std::ostream& out_stream, const smt::noodler::parikh::Transition& transition) {
        out_stream << "Transition{.source=" << std::to_string(std::get<0>(transition))
                                            << ", .symbol=" << std::to_string(std::get<1>(transition))
                                            << ", .target=" << std::to_string(std::get<2>(transition))
                                            << "}";
        return out_stream;
    }
}

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
                    LenNode(LenFormulaType::LEQ, {0, this->gamma_fin[state]}),
                    LenNode(LenFormulaType::LEQ, {this->gamma_fin[state], 1})
                }) );
            } else {
                // gamma_fin[state] == 0
                phi_fin.succ.emplace_back( LenNode(LenFormulaType::EQ, {0, this->gamma_fin[state]}) );
            }
        }

        // There should be only 1 state that is final
        LenNode sum_of_gamma_fin (LenFormulaType::PLUS, {});
        for (BasicTerm& gamma_fin : this->gamma_fin) {
            sum_of_gamma_fin.succ.push_back(gamma_fin);
        }
        LenNode max_one_final_state (LenFormulaType::EQ, {sum_of_gamma_fin, 1});
        phi_fin.succ.push_back(max_one_final_state);

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
     * phi^2_q := sigma_q <= -1 => (gamma^I_q = 0 && (conj #t = 0 for each t = (.,.,q)) ) (if a state does not occurr on the
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
            // State has a distance 0 in the spanning tree iff it is the initial state
            LenNode cl1(LenFormulaType::AND, { // sigma_q = 0  <=>  gamma_init_q = 1
                LenNode(LenFormulaType::OR, {
                    LenNode(LenFormulaType::NEQ, {this->sigma[state], 0}),
                    LenNode(LenFormulaType::EQ, {this->gamma_init[state], 1}),
                }),
                LenNode(LenFormulaType::OR, {
                    LenNode(LenFormulaType::EQ, {this->sigma[state], 0}),
                    LenNode(LenFormulaType::NEQ, {this->gamma_init[state], 1}),
                }),
            });

            // Force all incoming transitions to be taken 0 times
            // @Optimize: maybe we could emit a sum of all transitions here: \sum(..) = 0, the LIA solver might be happier
            LenNode conj_prev(LenFormulaType::AND);
            for(const Transition& tr : prev_trans[state]) {
                conj_prev.succ.push_back(LenNode(LenFormulaType::EQ, {
                    this->trans.at(tr),
                    0
                }));
            }

            // If the state has negative sigma_q, then it is not visited at all - force all incoming transitions to be taken 0 times.
            LenNode minus_sigma (LenFormulaType::MINUS, {this->sigma[state]});
            LenNode cl2(LenFormulaType::OR, { // sigma_q <= -1  --> "all incoming transitions are taken 0 times"
                LenNode(LenFormulaType::LT, { minus_sigma, 1 }),  // in implication we have (sigma <= -1), rewriting implication we get (sigma > -1) <=> (-sigma < 1)
                LenNode(LenFormulaType::AND, {
                    LenNode(LenFormulaType::EQ, { this->gamma_init[state], 0 }),
                    conj_prev,
                })
            });

            // If the state q was visited during a run, it was reached from q' via some transition t.
            // There must be one transition reaching q first, therefore, generate a disjunction
            // across all incoming transitions t, such that if t is taken, then sigma_q = sigma_{q'} + 1
            LenNode disj_prev(LenFormulaType::OR);
            for(const Transition& tr : prev_trans[state]) {
                disj_prev.succ.push_back(LenNode(LenFormulaType::AND, {               // AND:
                    LenNode(LenFormulaType::LT, {0, this->trans.at(tr)}),             // - Transition was taken (0 < #t)
                    LenNode(LenFormulaType::LEQ, {0, this->sigma[std::get<0>(tr)]}),  // - The source state of the transition is reached within this run
                    LenNode(LenFormulaType::EQ, {                                     // - the distance of the current state is one bigger than the origin of the transition
                        this->sigma[state],
                        LenNode(LenFormulaType::PLUS, { this->sigma[std::get<0>(tr)], 1 }),
                    })
                }));
            }
            LenNode cl3(LenFormulaType::OR, {  // (sigma_q > 0) --> "above formula forcing correct value of sigma_q"
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

        LenNode force_new_vars_expressing_str_vars_length = get_var_length(diseq.get_set());
        STRACE("str-diseq", tout << "* get_var_length:  " << std::endl << force_new_vars_expressing_str_vars_length << std::endl << std::endl;);

        LenNode diff_symbol = get_diff_symbol_formula();
        STRACE("str-diseq", tout << "* get_diff_symbol_formula:  " << std::endl << diff_symbol << std::endl << std::endl;);

        LenNode result = LenNode(LenFormulaType::AND, {
            parikh,
            force_new_vars_expressing_str_vars_length,
            LenNode(LenFormulaType::OR, {
                diseq_len,
                LenNode(LenFormulaType::AND, {
                    mismatch,
                    diff_symbol
                })
            })
        });

        return result;
    }

    LenNode ParikhImageDiseqTag::get_formula_for_multiple_diseqs(const std::vector<Predicate>& disequations) {
        this->predicates = disequations;
        init_mismatch_pos_inside_vars_per_diseq();

        LenNode parikh_image_formula = compute_parikh_image();

        STRACE("str-diseq", tout << "* (multiple-disequations) Parikh image symbols:  " << std::endl;
            for(const auto& [sym, bt] : this->tag_occurence_count_vars) {
                tout << bt.to_string() << " : " << sym.to_string() << std::endl;
            }
            tout << std::endl;
        );
        STRACE("str-diseq", tout << "* (multiple-disequations) compute_parikh_image:  " << std::endl << parikh_image_formula << std::endl << std::endl;);

        LenNode all_disequations_have_samples = make_sure_every_disequation_has_symbols_sampled();
        STRACE("str-diseq", tout << "* every disequation should have a symbol sampled:  " << std::endl << all_disequations_have_samples << std::endl << std::endl;);

        LenNode all_register_variables_have_values = assert_register_values();
        STRACE("str-diseq", tout << "* all registers hold correct values wrt. run:  " << std::endl << all_register_variables_have_values << std::endl << std::endl;);

        std::set<BasicTerm> all_vars;  // @Todo(mhecko): We are doing something similar elsewhere in the codebase, refactor.
        for (auto& disequation : disequations) {
            all_vars.insert(disequation.get_left_side().begin(), disequation.get_left_side().end());
            all_vars.insert(disequation.get_right_side().begin(), disequation.get_right_side().end());
        }

        LenNode force_new_vars_expressing_str_vars_length = get_var_length(all_vars);
        STRACE("str-diseq", tout << "* binding variable lengths to <L, var> occurrences:  " << std::endl << force_new_vars_expressing_str_vars_length << std::endl << std::endl;);

        LenNode all_copies_are_correct = assert_copy_transition_correctness();
        STRACE("str-diseq", tout << "* making <C, X..> transitions can be taken if there is some <R, X..> transition taken before:  " << std::endl << all_copies_are_correct << std::endl << std::endl;);

        LenNode all_disequations_are_satisfied (LenFormulaType::AND, {});
        for (int disequation_idx = 0; disequation_idx < static_cast<int>(disequations.size()); disequation_idx++) {
            LenNode disequation_contains_a_conflict = make_mismatch_existence_assertion_for_diseq(disequation_idx);
            LenNode disequation_sides_have_different_length = get_diseq_length(disequations.at(disequation_idx));

            LenNode either_different_lengths_or_conflict (LenFormulaType::OR, {disequation_contains_a_conflict, disequation_sides_have_different_length });
            all_disequations_are_satisfied.succ.push_back(either_different_lengths_or_conflict);
        }

        LenNode resulting_formula (LenFormulaType::AND, {
            parikh_image_formula,
            all_copies_are_correct,
            all_disequations_have_samples,
            all_register_variables_have_values,
            all_disequations_are_satisfied
        });

        return resulting_formula;
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
        size_t current_term_idx = 0;
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

    LenNode ParikhImageDiseqTag::count_register_stores_for_var_and_side(BasicTerm& var, int predicate_side_label) const {
        LenNode register_store_count (LenFormulaType::PLUS);
        for (const ca::AtomicSymbol& atomic_symbol : this->atomic_symbols) {
            bool is_register_store = (atomic_symbol.type == ca::AtomicSymbol::TagType::REGISTER_STORE);
            bool matches_var  = (atomic_symbol.var == var);
            bool matches_side = (atomic_symbol.copy_idx == predicate_side_label);

            if (is_register_store && matches_var && matches_side) {
                const BasicTerm& symbol_count_var = this->tag_occurence_count_vars.at(atomic_symbol);
                register_store_count.succ.push_back(LenNode(symbol_count_var));
            }
        }
        return register_store_count;
    }


    std::pair<LenNode, LenNode> ParikhImageDiseqTag::express_mismatch_position(const std::vector<BasicTerm>& predicate_side, size_t mismatch_pos, size_t sample_order_label, const LenNode* offset_var) const {
        const BasicTerm& var = predicate_side[mismatch_pos];
        LenNode mismatch_pos_formula = express_string_length_preceding_supposed_mismatch(predicate_side, mismatch_pos);
        // add symbol <P, var, label_left, 0> where var is i-th variable on left side of diseq
        ca::AtomicSymbol mismatch_pos_sym = ca::AtomicSymbol::create_p_symbol(var, sample_order_label);
        auto mismatch_sym_var_it = this->tag_occurence_count_vars.find(mismatch_pos_sym);
        if (mismatch_sym_var_it == this->tag_occurence_count_vars.end()) {
            return std::make_pair(LenNode(LenFormulaType::FALSE), 0);  // The mismatch guess is not possible
        }

        if (offset_var != nullptr) {
            mismatch_pos_formula.succ.push_back(*offset_var);
        }

        return std::make_pair(mismatch_pos_formula, LenNode(mismatch_sym_var_it->second));
    }

    LenNode make_guess_what_side_sees_mismatch_first(const LenNode& lhs_sum, const LenNode& lhs_mismatch_in_var, const LenNode& rhs_sum, const LenNode& rhs_mismatch_in_var, bool mismatch_pos_subsume_each_other = false) {
        LenNode mismatch_position_case_split (LenFormulaType::OR, {});

        {
            LenNode lhs_sees_mismatch_sooner = lhs_sum;
            lhs_sees_mismatch_sooner.succ.push_back(lhs_mismatch_in_var);  // Result: <L, x> + ... <L, z> + <P, var, 2> + <P, var, 1>

            LenNode rhs_sees_mismatch_later = rhs_sum;
            if (!mismatch_pos_subsume_each_other) {
                rhs_sees_mismatch_later.succ.push_back(lhs_mismatch_in_var);  // Result: <L, x> + ... <L, z> + <P, var, 2> + <P, var, 1>
            }
            rhs_sees_mismatch_later.succ.push_back(rhs_mismatch_in_var);  // Result: <L, x> + ... <L, z> + <P, var, 2> + <P, var, 1> + <P, var, 2>

            LenNode branch(LenFormulaType::EQ, {lhs_sees_mismatch_sooner, rhs_sees_mismatch_later});
            mismatch_position_case_split.succ.push_back(branch);
        }

        // (lhs > rhs) rhs sees mismatch sooner than lhs
        {
            // When building the sum for both sides, we pass in which of the variables should be seen first to generate correct <P, var, ORD> var to add
            // In the case when (var_right == var_left) we always pass ORD=1 for var_left, and ORD=2 for var_right, so we know that rhs_position_inside_var = <P, X, 2>
            LenNode lhs_sees_mismatch_later = lhs_sum;
            if (!mismatch_pos_subsume_each_other) {
                lhs_sees_mismatch_later.succ.push_back(lhs_mismatch_in_var); // Result: <L, x> + ... <L, z> + <P, var, 1>
            }
            lhs_sees_mismatch_later.succ.push_back(rhs_mismatch_in_var); // Result: <L, x> + ... <L, z> + <P, var, 1> + <P, var, 2>

            LenNode rhs_sees_mismatch_sooner = rhs_sum;
            rhs_sees_mismatch_sooner.succ.push_back(lhs_mismatch_in_var); // <L, x> + ... <L, z> + <P, var, 1>

            LenNode branch(LenFormulaType::EQ, {lhs_sees_mismatch_later, rhs_sees_mismatch_sooner});
            mismatch_position_case_split.succ.push_back(branch);
        }

        return mismatch_position_case_split;
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
        int label_left = 1, label_right = 2;
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

        auto [lhs_mismatch_pos_expr, lhs_position_inside_var] = express_mismatch_position(diseq.get_left_side(), left_mismatch_pos, label_left);
        if (lhs_mismatch_pos_expr.type == LenFormulaType::FALSE) return lhs_mismatch_pos_expr;

        auto [rhs_mismatch_pos_expr, rhs_position_inside_var] = express_mismatch_position(diseq.get_right_side(), right_mismatch_pos, label_right, &rhs_offset);
        if (rhs_mismatch_pos_expr.type == LenFormulaType::FALSE) return rhs_mismatch_pos_expr;

        LenNode lhs_register_stores_cnt = count_register_stores_for_var_and_side(var_left, label_left);
        LenNode lhs_has_register_store(LenFormulaType::LEQ, { 1, lhs_register_stores_cnt });

        LenNode rhs_register_stores_cnt = count_register_stores_for_var_and_side(var_right, label_right);
        LenNode rhs_has_register_store(LenFormulaType::LEQ, { 1, rhs_register_stores_cnt });

        if (var_right != var_left) { // Simple case, we know whose mismatch symbol will be sampled first
            // No need to do any magic with the position_inside_var (e.g. #<P, X, 1>) vars
            lhs_mismatch_pos_expr.succ.push_back(lhs_position_inside_var);
            rhs_mismatch_pos_expr.succ.push_back(rhs_position_inside_var);

            LenNode mismatch_position_is_same(LenFormulaType::EQ, { lhs_mismatch_pos_expr, rhs_mismatch_pos_expr});

            return LenNode(LenFormulaType::AND, {
                mismatch_position_is_same,
                lhs_has_register_store,
                rhs_has_register_store
            });
        }

        // #Note(mhecko): These two top-level conjuncts should be redundant - the automaton structure should force
        //                seeing at least one <P, x, 1> and <P, x, 2> symbols. Therefore, it should not be
        //                necessary to prevent from trivial solutions 0=0.
        // LenNode some_lhs_mismatch_seen(LenFormulaType::LEQ, { 1, LenNode(first_mismatch_sym_var_it->second) });
        // LenNode some_rhs_mismatch_seen(LenFormulaType::LEQ, { 1, LenNode(second_mismatch_sym_var_it->second) });

        // If left_var == right_var, we don't know which sample will be seen first - create a disjunction for both branches
        LenNode mismatch_position_case_split = make_guess_what_side_sees_mismatch_first(lhs_mismatch_pos_expr, lhs_position_inside_var,
                                                                                        rhs_mismatch_pos_expr, rhs_position_inside_var);

        return LenNode(LenFormulaType::AND, {
            mismatch_position_case_split,
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
                    ca::AtomicSymbol counterpart = ca::AtomicSymbol::create_r_symbol(var_node.atom_val, (ats.copy_idx == 1 ? char(2) : char(1)), ats.symbol);

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

    LenNode ParikhImageDiseqTag::make_sure_every_disequation_has_symbols_sampled() const {
        // We have two kinds of "sampling" transitions:
        // <C, var, disequation, side, copy_idx>
        // <R, disequation, side, mismatch_idx, alphabet_symbol>
        // Therefore, for any disequation D and its side S we need to have:
        //    #<C, var, D, S, copy_idx> + #<R, disequation, side, mismatch_idx, alphabet_symbol> = 1
        std::unordered_map<std::pair<size_t, ca::AtomicSymbol::PredicateSide>, std::vector<LenNode>> sampling_transitions_per_diseq_side;

        // Collect variables that need to add to one for every (predicate, side)
        for (const auto& [transition, transition_var] : this->get_trans_vars()) {
            mata::nfa::State source_state  = std::get<0>(transition);
            mata::Symbol     symbol_handle = std::get<1>(transition);
            mata::nfa::State target_state  = std::get<2>(transition);

            // @Note: We probably could use state metadata to accelerate this a bit more
            size_t source_level = this->ca.metadata.levels[source_state];
            size_t target_level = this->ca.metadata.levels[target_state];

            bool is_sampling_transition = ((source_level+1) == target_level);
            if (!is_sampling_transition) continue;

            const TagSet& tag_set = ca.alph.get_symbol(symbol_handle);

            std::pair<size_t, AtomicSymbol::PredicateSide> disequation_side;
            bool disequation_side_info_found = false;
            for (const auto& tag: tag_set) {
                if (tag.type == AtomicSymbol::TagType::COPY_PREVIOUS || tag.type == AtomicSymbol::TagType::REGISTER_STORE) {
                    disequation_side = std::make_pair(tag.predicate_idx, tag.predicate_side);
                    disequation_side_info_found = true;
                }
            }

            if (!disequation_side_info_found) {
                std::cout << "Failed to find disequation side info for transition " << transition
                          << ". Atomic symbol on edge: " << tag_set << std::endl;
            }

            assert(disequation_side_info_found); // Transition is crossing levels - it should be either Copy or Sampling

            sampling_transitions_per_diseq_side[disequation_side].push_back(transition_var);
        }

        LenNode conjunction_across_all_disequations(LenFormulaType::AND, {});
        for (const auto& [disequation_side, vars] : sampling_transitions_per_diseq_side) {
            LenNode sum (LenFormulaType::PLUS, vars);
            LenNode equation_for_this_diseq_side (LenFormulaType::EQ, {sum, 1});
            conjunction_across_all_disequations.succ.push_back(equation_for_this_diseq_side);
        }

        return conjunction_across_all_disequations;
    }

    LenNode ParikhImageDiseqTag::assert_register_values() {
        int predicate_count   = static_cast<int>(this->get_predicate_count());
        int register_count = 2*predicate_count; // Every predicate has 2 sides
        int max_mismatch_sample = 2*predicate_count+1; // Every predicate has 2 sides

        this->registers_in_sampling_order.clear();
        this->registers_in_sampling_order.reserve(register_count);

        // Populate registers in sampling order
        for (int register_idx = 0; register_idx < register_count; register_idx++) {
            std::string var_name = "reg_ord" + std::to_string(register_idx);
            BasicTerm var = BasicTerm(BasicTermType::Variable, var_name);
            LenNode var_node (var);
            this->registers_in_sampling_order.push_back(var_node);
        }

        this->registers_per_disequation_side.clear(); // Technically, this should not be needed

        for (int predicate_idx = 0; predicate_idx < predicate_count; predicate_idx++) {
            DiseqSide lhs = {predicate_idx, AtomicSymbol::PredicateSide::LEFT};
            DiseqSide rhs = {predicate_idx, AtomicSymbol::PredicateSide::RIGHT};

            std::string lhs_var_name = "reg_diseq" + std::to_string(predicate_idx) + "_left";
            std::string rhs_var_name = "reg_diseq" + std::to_string(predicate_idx) + "_right";

            BasicTerm lhs_var = BasicTerm(BasicTermType::Variable, lhs_var_name);
            BasicTerm rhs_var = BasicTerm(BasicTermType::Variable, rhs_var_name);

            this->registers_per_disequation_side.emplace(lhs, lhs_var);
            this->registers_per_disequation_side.emplace(rhs, rhs_var);
        }

        LenNode all_registers_have_value_conjunction (LenFormulaType::AND, {});
        all_registers_have_value_conjunction.succ.reserve(register_count);

        // Prepare disjunctions for every automaton level forcing value of the corresponding reg_ord<i>
        for (int register_idx = 0; register_idx < register_count; register_idx++) {
            all_registers_have_value_conjunction.succ.push_back(LenNode(LenFormulaType::AND, {}));
        }

        for (const auto& [transition, var] : this->get_trans_vars()) {
            mata::nfa::State source_state  = std::get<0>(transition);
            mata::Symbol     symbol_handle = std::get<1>(transition);
            mata::nfa::State target_state  = std::get<2>(transition);

            size_t source_level = ca.metadata.levels[source_state];
            size_t target_level = ca.metadata.levels[target_state];

            if (source_level == target_level) continue; // This transition is not Copy nor Register_Store

            const TagSet& tag_set = ca.alph.get_symbol(symbol_handle);

            AtomicSymbol::TagType transition_type;
            DiseqSide diseq_side;
            int mismatch_level = -1;
            mata::Symbol sampled_symbol;

            // Look at the tags and determine what disequation and side are we sampling
            for (const AtomicSymbol& tag : tag_set) {
                if (tag.type == AtomicSymbol::TagType::REGISTER_STORE) {
                    mismatch_level = static_cast<int>(tag.copy_idx);
                    diseq_side = {.predicate_idx = tag.predicate_idx, .side = tag.predicate_side};
                    transition_type = tag.type;
                    sampled_symbol = tag.symbol;
                }

                if (tag.type == AtomicSymbol::TagType::COPY_PREVIOUS) {
                    mismatch_level = static_cast<int>(tag.copy_idx);
                    diseq_side = {.predicate_idx = tag.predicate_idx, .side = tag.predicate_side};
                    transition_type = tag.type;
                }
            }

            assert(mismatch_level >= 0);

            int mismatch_idx = mismatch_level - 1;

            LenNode& conjunction_for_this_mismatch_idx = all_registers_have_value_conjunction.succ[mismatch_idx];

            if (transition_type == AtomicSymbol::TagType::COPY_PREVIOUS) {
                if (mismatch_idx == 0) {
                    std::cout << "Cannot have copy transitions from the first level - there is no register value to copy!\n";
                    assert (mismatch_idx != 0);  // Fail
                }
                // Add an implicication:
                //  (#<C, Var, disequation_idx, side, mismatch_level>  > 0) -> reg_ord{mismatch_level} = reg_ord{mismatch_level-1}
                //  (#<C, Var, disequation_idx, side, mismatch_level> <= 0) OR reg_ord{mismatch_level} = reg_ord{mismatch_level-1}
                LenNode implication_lhs (LenFormulaType::LEQ, {var, 0});

                const LenNode& ith_register_var      = this->registers_in_sampling_order[mismatch_idx];
                const LenNode& previous_register_var = this->registers_in_sampling_order[mismatch_idx-1];

                const LenNode& diseq_side_register = this->registers_per_disequation_side.at(diseq_side);

                LenNode set_ith_register        (LenFormulaType::EQ, {ith_register_var,    previous_register_var});
                LenNode set_diseq_side_register (LenFormulaType::EQ, {diseq_side_register, previous_register_var});

                LenNode implication_rhs (LenFormulaType::AND, {set_ith_register, set_diseq_side_register});
                LenNode disjunction_equiv_to_implication (LenFormulaType::OR, {implication_lhs, implication_rhs});

                conjunction_for_this_mismatch_idx.succ.push_back(disjunction_equiv_to_implication);
                continue;
            }

            if (transition_type == AtomicSymbol::TagType::REGISTER_STORE) {
                // Add an implicication:
                //  (#<R, Var, disequation_idx, side, mismatch_level, A>  > 0) -> reg_ord{mismatch_level} = A
                //  (#<R, Var, disequation_idx, side, mismatch_level, A> <= 0) OR reg_ord{mismatch_level} = A
                LenNode implication_lhs (LenFormulaType::LEQ, {var, 0});

                const LenNode& ith_register_var    = this->registers_in_sampling_order[mismatch_idx];
                const LenNode& diseq_side_register = this->registers_per_disequation_side.at(diseq_side);

                LenNode sampled_symbol_node (sampled_symbol);

                LenNode set_ith_register        (LenFormulaType::EQ, {ith_register_var,    sampled_symbol_node});
                LenNode set_diseq_side_register (LenFormulaType::EQ, {diseq_side_register, sampled_symbol_node});

                LenNode implication_rhs (LenFormulaType::AND, {set_ith_register, set_diseq_side_register});
                LenNode disjunction_equiv_to_implication (LenFormulaType::OR, {implication_lhs, implication_rhs});

                conjunction_for_this_mismatch_idx.succ.push_back(disjunction_equiv_to_implication);
                continue;
            }
        }

        return all_registers_have_value_conjunction;
    }

    LenNode ParikhImageDiseqTag::make_formula_binding_mismatch_pos_with_implications(const LenNode& var_to_restrict, const std::vector<std::vector<LenNode>>& control_vars_per_level, const BasicTerm& var_containing_mismatch) const {
        std::vector<const BasicTerm*> mismatch_pos_transition_vars (2*this->get_predicate_count());

        for (const auto& [tag, tag_count_var] : this->tag_occurence_count_vars) {
            if (tag.type != AtomicSymbol::TagType::MISMATCH_POS) continue;
            if (tag.var != var_containing_mismatch) continue;
            size_t target_level = tag.copy_idx - 1;
            mismatch_pos_transition_vars[target_level] = &tag_count_var;
        }

        LenNode conjunction_of_implications (LenFormulaType::AND);

        for (size_t level_idx = 0; level_idx < control_vars_per_level.size(); level_idx++) {
            const std::vector<LenNode>& control_var_for_this_level = control_vars_per_level[level_idx];
            LenNode sum_of_control_vars (LenFormulaType::PLUS, control_var_for_this_level);

            // Positive: control_var_1 + ... + control_var_n  > 0
            // Negated : control_var_1 + ... + control_var_n <= 0
            LenNode negated_antecedent (LenFormulaType::LEQ, {sum_of_control_vars, 0});

            LenNode sum_of_pos_tags (LenFormulaType::PLUS);
            for (size_t pos_tag_level_idx = 0; pos_tag_level_idx <= level_idx; pos_tag_level_idx++) {
                const BasicTerm* pos_tag_occurrence_count = mismatch_pos_transition_vars[pos_tag_level_idx];
                assert(pos_tag_occurrence_count != nullptr);
                sum_of_pos_tags.succ.push_back(*pos_tag_occurrence_count);
            }

            LenNode consequent (LenFormulaType::EQ, {var_to_restrict, sum_of_pos_tags});

            // Make an implication:
            //   control_var_1 + ... + control_var_n > 0 --> var_to_restrict = <P, X, 1> + <P, X, 2> + ... <P, X, $level>
            LenNode implication (LenFormulaType::OR, {negated_antecedent, consequent});
            conjunction_of_implications.succ.push_back(implication);
        }

        return conjunction_of_implications;
    }

    void ParikhImageDiseqTag::init_mismatch_pos_inside_vars_per_diseq() {
        for (size_t predicate_idx = 0; predicate_idx < this->get_predicate_count(); predicate_idx++) {
            std::string lhs_mismatch_pos_var_name = "mismatch_pos_" + std::to_string(predicate_idx) + "_L";
            std::string rhs_mismatch_pos_var_name = "mismatch_pos_" + std::to_string(predicate_idx) + "_R";

            BasicTerm lhs_mismatch_pos_var (BasicTermType::Variable, lhs_mismatch_pos_var_name);
            BasicTerm rhs_mismatch_pos_var (BasicTermType::Variable, rhs_mismatch_pos_var_name);

            this->mismatch_pos_inside_vars_per_diseq.emplace(predicate_idx, std::make_pair(lhs_mismatch_pos_var, rhs_mismatch_pos_var));
        }
    }

    LenNode ParikhImageDiseqTag::make_mismatch_pos_vars_assertion(int predicate_idx, const BasicTerm& left_var, const BasicTerm& right_var) const {
        // @Todo(mhecko): unused, refactor?
        std::vector<std::vector<LenNode>> control_vars_per_level_for_lhs, control_vars_per_level_for_rhs;
        control_vars_per_level_for_lhs.resize(2*this->get_predicate_count());
        control_vars_per_level_for_rhs.resize(2*this->get_predicate_count());

        for (const auto& [tag, tag_occurrence_count] : this->tag_occurence_count_vars) {
            if (!tag.is_mutating_registers())       continue;
            if (tag.predicate_idx != predicate_idx) continue;

            size_t control_level = tag.copy_idx - 1;
            if (tag.predicate_side == AtomicSymbol::PredicateSide::LEFT) {
                control_vars_per_level_for_lhs[control_level].push_back(tag_occurrence_count);
            } else {
                control_vars_per_level_for_rhs[control_level].push_back(tag_occurrence_count);
            }
        }

        const auto& predicate_mismatch_var_pair = this->mismatch_pos_inside_vars_per_diseq.at(predicate_idx);
        const BasicTerm& lhs_mismatch_pos_var = predicate_mismatch_var_pair.first;
        const BasicTerm& rhs_mismatch_pos_var = predicate_mismatch_var_pair.second;

        LenNode lhs_mismatch_pos_val_formula = make_formula_binding_mismatch_pos_with_implications(lhs_mismatch_pos_var, control_vars_per_level_for_lhs, left_var);
        LenNode rhs_mismatch_pos_val_formula = make_formula_binding_mismatch_pos_with_implications(rhs_mismatch_pos_var, control_vars_per_level_for_rhs, right_var);

        LenNode result (LenFormulaType::AND, {lhs_mismatch_pos_val_formula, rhs_mismatch_pos_val_formula});

        return result;
    }

    std::vector<std::vector<LenNode>> ParikhImageDiseqTag::collect_sampling_transisions_for_diseq_and_var(const BasicTerm& var, int diseq_idx, AtomicSymbol::PredicateSide side) const {
        std::vector<std::vector<LenNode>> sampling_transitions_per_automaton_level;
        sampling_transitions_per_automaton_level.resize(2*this->get_predicate_count());

        for (const auto& [tag, tag_var] : this->tag_occurence_count_vars) {
            if (!tag.is_mutating_registers()) continue;

            if (tag.var != var || tag.predicate_idx != diseq_idx || tag.predicate_side != side) {
                continue;
            }

            sampling_transitions_per_automaton_level[tag.copy_idx - 1].push_back(tag_var);
        }

        return sampling_transitions_per_automaton_level;
    }

    LenNode make_register_contents_differ_formula(const std::map<DiseqSide, LenNode>& register_contents_vars, int predicate_idx) {
        DiseqSide lhs = {.predicate_idx = static_cast<int>(predicate_idx), .side = AtomicSymbol::PredicateSide::LEFT};
        const LenNode& lhs_symbol = register_contents_vars.at(lhs);

        DiseqSide rhs = {.predicate_idx = static_cast<int>(predicate_idx), .side = AtomicSymbol::PredicateSide::RIGHT};
        const LenNode& rhs_symbol = register_contents_vars.at(rhs);

        mata::Symbol dummy_symbol = noodler::util::get_dummy_symbol();
        LenNode lhs_symbol_is_dummy (LenFormulaType::EQ, {lhs_symbol, static_cast<int>(dummy_symbol)});
        LenNode rhs_symbol_is_dummy (LenFormulaType::EQ, {rhs_symbol, static_cast<int>(dummy_symbol)});

        LenNode symbols_differ (LenFormulaType::NEQ, {lhs_symbol, rhs_symbol});

        LenNode symbols_must_differ_if_not_dummy (LenFormulaType::OR, {
            lhs_symbol_is_dummy,
            rhs_symbol_is_dummy,
            symbols_differ
        });

        return symbols_must_differ_if_not_dummy;
    }

    LenNode assert_one_of_the_transitions_taken(const std::vector<std::vector<LenNode>>& transitions) {
        LenNode sum_of_all_transitions (LenFormulaType::PLUS, {});

        for (auto& transition_list : transitions) {
            for (auto& var : transition_list) {
                sum_of_all_transitions.succ.push_back(var);
            }
        }

        return LenNode(LenFormulaType::LT, {0, sum_of_all_transitions});
    }

    struct SamplingTransitionLists {
        std::vector<LenNode> register_stores;
        std::vector<LenNode> copies;
    };


    LenNode ParikhImageDiseqTag::assert_copy_transition_correctness() const {
        std::map<BasicTerm, std::vector<SamplingTransitionLists>> sampling_transitions_grouped_by_var;
        std::map<BasicTerm, std::vector<const BasicTerm*>> var_to_mismatch_pos_tag_counts;

        std::set<BasicTerm> all_vars;
        for (auto& diseq : this->predicates) {
            all_vars.insert(diseq.get_left_side().begin(), diseq.get_left_side().end());
            all_vars.insert(diseq.get_right_side().begin(), diseq.get_right_side().end());
        }

        for (const BasicTerm& var : all_vars) {
            sampling_transitions_grouped_by_var[var].resize(2*get_predicate_count());
            var_to_mismatch_pos_tag_counts[var].resize(2*get_predicate_count());
        }

        for (const auto& [tag, tag_var] : tag_occurence_count_vars) {

            if (tag.type == AtomicSymbol::TagType::MISMATCH_POS) {
                var_to_mismatch_pos_tag_counts.at(tag.var)[tag.copy_idx-1] = &tag_var;
                continue;
            }

            if (!tag.is_mutating_registers()) continue;

            std::vector<SamplingTransitionLists>& transitions_for_this_var = sampling_transitions_grouped_by_var.at(tag.var);
            SamplingTransitionLists& this_level_transitions = transitions_for_this_var[tag.copy_idx-1];

            if (tag.type == AtomicSymbol::TagType::REGISTER_STORE) {
                this_level_transitions.register_stores.push_back(tag_var);
            }

            if (tag.type == AtomicSymbol::TagType::COPY_PREVIOUS) {
                this_level_transitions.copies.push_back(tag_var);
            }
        }

        /**
         * If we did not to the current level into a state belonging to the variable X by sampling or copying,
         * then we cannot take a copy transition - the register does not hold value that belongs to X. Otherwise
         * we could take a copy transition a copy register value that belongs to other variable.
         *
         * #<C, X, ?, ?, previous_level> + #<R, X, ?, ?, previous_level> = 0  --->  #<C, X, ?, ?, current_level> = 0
         */
        LenNode copies_copy_register_values_from_the_sampled_var (LenFormulaType::AND, {});  // Correctness across all variables
        for (const auto& [var, sampling_transitions] : sampling_transitions_grouped_by_var) {
            LenNode copies_for_this_var_are_correct (LenFormulaType::AND, {});

            for (size_t transition_level = 1; transition_level < sampling_transitions.size(); transition_level++) {
                const SamplingTransitionLists& previous_level = sampling_transitions[transition_level-1];
                const SamplingTransitionLists& current_level  = sampling_transitions[transition_level];

                LenNode sum_of_sampling_for_previous_level (LenFormulaType::PLUS, previous_level.copies);
                for (auto& register_store : previous_level.register_stores) {
                   sum_of_sampling_for_previous_level.succ.push_back(register_store);
                }
                LenNode previous_level_has_no_value_to_copy (LenFormulaType::NEQ, {sum_of_sampling_for_previous_level, 0}); // Already negated, we will write implication as (not antecendent OR consequent)

                LenNode sum_of_copies_for_current_level (LenFormulaType::PLUS, current_level.copies);
                LenNode current_level_performs_no_copies (LenFormulaType::EQ, {sum_of_copies_for_current_level, 0});

                LenNode asserting_implication (LenFormulaType::OR, {previous_level_has_no_value_to_copy, current_level_performs_no_copies});

                copies_for_this_var_are_correct.succ.push_back(asserting_implication);
            }
            copies_copy_register_values_from_the_sampled_var.succ.push_back(copies_for_this_var_are_correct);
        }


        /**
         * If we are at level L and we do a copy transitions for variable X, we cannot take any normal transitions at level L.
         * Otherwise we might compute offset inside variable that is wrong.
         *
         * #<C, X, ?, ?, level> > 0  --->  #<P, X, level-1> = 0
         */
        LenNode cannot_take_normal_transitions_before_copying (LenFormulaType::AND, {});
        for (const auto& [var, sampling_transitions] : sampling_transitions_grouped_by_var) {
            for (size_t level = 1; level < sampling_transitions.size(); level++) {
                const SamplingTransitionLists& level_mutating_transitions = sampling_transitions[level];

                LenNode sum_of_copies_from_this_level (LenFormulaType::PLUS, level_mutating_transitions.copies);
                LenNode this_level_did_a_copy (LenFormulaType::LEQ, {sum_of_copies_from_this_level, 0}); // Already negated, we will write implication as (not antecendent OR consequent)

                const BasicTerm* transitions_at_this_level_var = var_to_mismatch_pos_tag_counts.at(var).at(level);
                LenNode tranistions_at_this_level_node (*transitions_at_this_level_var);
                LenNode no_ordinary_transitions_at_this_level (LenFormulaType::EQ, {tranistions_at_this_level_node, 0});


                LenNode asserting_implication (LenFormulaType::OR, {this_level_did_a_copy, no_ordinary_transitions_at_this_level});

                cannot_take_normal_transitions_before_copying.succ.push_back(asserting_implication);
            }
        }

        LenNode result (LenFormulaType::AND, {copies_copy_register_values_from_the_sampled_var, cannot_take_normal_transitions_before_copying});
        return result;
    }

    LenNode ParikhImageDiseqTag::make_mismatch_existence_assertion_for_diseq(size_t predicate_idx) const {
        const Predicate& disequation = this->predicates[predicate_idx];

        LenNode disjunction_across_all_var_pairs(LenFormulaType::OR, {});

        for (size_t left_var_idx = 0; left_var_idx < disequation.get_left_side().size(); left_var_idx++) {
            for (size_t right_var_idx = 0; right_var_idx < disequation.get_right_side().size(); right_var_idx++) {
                // Sum up all <L, x> that preceed the left_var_idx and right_var_idx
                LenNode lhs_mismatch_pos_sum = express_string_length_preceding_supposed_mismatch(disequation.get_left_side(), left_var_idx);
                LenNode rhs_mismatch_pos_sum = express_string_length_preceding_supposed_mismatch(disequation.get_right_side(), right_var_idx);

                const BasicTerm& left_var  = disequation.get_left_side().at(left_var_idx);
                const BasicTerm& right_var = disequation.get_right_side().at(right_var_idx);

                const auto& [left_mismatch_pos_var, right_mismatch_pos_var] = this->mismatch_pos_inside_vars_per_diseq.at(predicate_idx);

                auto sampling_transitions_for_left_var = collect_sampling_transisions_for_diseq_and_var(left_var, predicate_idx, AtomicSymbol::PredicateSide::LEFT);
                LenNode left_mismatch_pos_is_correct = make_formula_binding_mismatch_pos_with_implications(left_mismatch_pos_var, sampling_transitions_for_left_var, left_var);

                auto sampling_transitions_for_right_var = collect_sampling_transisions_for_diseq_and_var(right_var, predicate_idx, AtomicSymbol::PredicateSide::RIGHT);
                LenNode right_mismatch_pos_is_correct = make_formula_binding_mismatch_pos_with_implications(right_mismatch_pos_var, sampling_transitions_for_right_var, right_var);

                LenNode symbols_differ = make_register_contents_differ_formula(this->registers_per_disequation_side, static_cast<int>(predicate_idx));

                // We have to take at least one of these transitions to see mismatch in left_var
                LenNode mismatch_seen_in_lhs_var = assert_one_of_the_transitions_taken(sampling_transitions_for_left_var);
                LenNode mismatch_seen_in_rhs_var = assert_one_of_the_transitions_taken(sampling_transitions_for_right_var);

                LenNode mismatch_pos_equal_and_registers_differ (LenFormulaType::AND, {
                    symbols_differ,           // Register contents differ
                    mismatch_seen_in_lhs_var, // One mismatch has been seen in the guessed left variable
                    mismatch_seen_in_rhs_var, // Other mismatch has been seen in the guessed right variable
                    left_mismatch_pos_is_correct, // The position inside left variable is correct wrt. where we have seen the conflict
                    right_mismatch_pos_is_correct // The position inside right variable is correct wrt. where we have seen the conflict
                });

                if (left_var != right_var) {
                    // No special magic needed, just add the mismatch positions
                    lhs_mismatch_pos_sum.succ.push_back(left_mismatch_pos_var);
                    rhs_mismatch_pos_sum.succ.push_back(right_mismatch_pos_var);

                    LenNode mismatch_positions_equal (LenFormulaType::EQ, {lhs_mismatch_pos_sum, rhs_mismatch_pos_sum});

                    mismatch_pos_equal_and_registers_differ.succ.push_back(mismatch_positions_equal);
                    disjunction_across_all_var_pairs.succ.push_back(mismatch_pos_equal_and_registers_differ);
                } else {
                    // We are dealing with the same variables - guess whether lhs sees mismatch first
                    LenNode mismatch_guess = make_guess_what_side_sees_mismatch_first(lhs_mismatch_pos_sum, left_mismatch_pos_var,
                                                                                      rhs_mismatch_pos_sum, right_mismatch_pos_var,
                                                                                      true);

                    mismatch_pos_equal_and_registers_differ.succ.push_back(mismatch_guess);
                    disjunction_across_all_var_pairs.succ.push_back(mismatch_pos_equal_and_registers_differ);
                }
            }
        }

        return disjunction_across_all_var_pairs;
    }

    LenNode ParikhImageNotContTag::get_nt_all_mismatch_formula(const Predicate& not_cont) {
        LenNode mismatch(LenFormulaType::OR);
        for(size_t i = 0; i < not_cont.get_haystack().size(); i++) {
            for (size_t j = 0; j < not_cont.get_needle().size(); j++) {
                mismatch.succ.push_back(get_mismatch_formula(i, j, not_cont, this->offset_var));
            }
        }
        return mismatch;
    }

    LenNode ParikhImageNotContTag::mk_rhs_longer_than_lhs_formula(const Predicate& not_contains) {

        std::unordered_map<BasicTerm, int> lhs_var_occurence_occurence_diff;

        for (const BasicTerm& term: not_contains.get_haystack()) {
            auto [old_map_entry, did_emplace_happen] = lhs_var_occurence_occurence_diff.emplace(term, 1);
            if (!did_emplace_happen) {
                old_map_entry->second += 1;
            }
        }

        for (const BasicTerm& term: not_contains.get_needle()) {
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
        return ca.metadata.where_is_state_copied_from[state];
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

        for (auto& [tag, tag_var] : this->tag_occurence_count_vars) {
            formula = LenNode(LenFormulaType::EXISTS,
                              {tag_var, formula});
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