#include <cassert>

#include "util/z3_exception.h"

#include "regex.h"
#include "theory_str_noodler.h"
#include "inclusion_graph.h"
#include "aut_assignment.h"

namespace {
    using mata::nfa::Nfa;
}

namespace smt::noodler::regex {

    void extract_symbols(expr* const ex, const seq_util& m_util_s, std::set<uint32_t>& alphabet) {
        if (m_util_s.str.is_string(ex)) {
            auto ex_app{ to_app(ex) };
            SASSERT(ex_app->get_num_parameters() == 1);
            const zstring string_literal{ zstring{ ex_app->get_parameter(0).get_zstring() } };
            for (size_t i{ 0 }; i < string_literal.length(); ++i) {
                alphabet.insert(string_literal[i]);
            }
            return;
        }

        if(util::is_variable(ex)) { // Skip variables.
            return;
        }

        SASSERT(is_app(ex));
        app* ex_app = to_app(ex);

        if (m_util_s.re.is_to_re(ex_app)) { // Handle conversion to regex function call.
            SASSERT(ex_app->get_num_args() == 1);
            const auto arg{ ex_app->get_arg(0) };
            // Assume that expression inside re.to_re() function is a string of characters.
            if (!m_util_s.str.is_string(arg)) { // if to_re has something other than string literal
                util::throw_error("we support only string literals in str.to_re");
            }
            extract_symbols(to_app(arg), m_util_s, alphabet);
            return;
        } else if (m_util_s.re.is_concat(ex_app) // Handle regex concatenation.
                || m_util_s.str.is_concat(ex_app) // Handle string concatenation.
                || m_util_s.re.is_intersection(ex_app) // Handle intersection.
            ) {
            for (unsigned int i = 0; i < ex_app->get_num_args(); ++i) {
                extract_symbols(to_app(ex_app->get_arg(i)), m_util_s, alphabet);
            }
            return;
        } else if (m_util_s.re.is_antimirov_union(ex_app)) { // Handle Antimirov union.
            util::throw_error("antimirov union is unsupported");
        } else if (m_util_s.re.is_complement(ex_app)) { // Handle complement.
            SASSERT(ex_app->get_num_args() == 1);
            const auto child{ ex_app->get_arg(0) };
            SASSERT(is_app(child));
            extract_symbols(to_app(child), m_util_s, alphabet);
            return;
        } else if (m_util_s.re.is_derivative(ex_app)) { // Handle derivative.
            util::throw_error("derivative is unsupported");
        } else if (m_util_s.re.is_diff(ex_app)) { // Handle diff.
            util::throw_error("regex difference is unsupported");
        } else if (m_util_s.re.is_dot_plus(ex_app)) { // Handle dot plus.
            // Handle repeated full char ('.+') (SMT2: (re.+ re.allchar)).
            return;
        } else if (m_util_s.re.is_empty(ex_app)) { // Handle empty language.
            return;
        } else if (m_util_s.re.is_epsilon(ex_app)) { // Handle epsilon.
            return;
        } else if (m_util_s.re.is_full_char(ex_app)) {
            // Handle full char (single occurrence of any string symbol, '.') (SMT2: re.allchar).
            return;
        } else if (m_util_s.re.is_full_seq(ex_app)) {
            // Handle full sequence of characters (any sequence of characters, '.*') (SMT2: re.all).
            return;
        } else if (m_util_s.re.is_of_pred(ex_app)) { // Handle of predicate.
            util::throw_error("of predicate is unsupported");
        } else if (m_util_s.re.is_opt(ex_app) // Handle optional.
                || m_util_s.re.is_plus(ex_app) // Handle positive iteration.
                || m_util_s.re.is_star(ex_app) // Handle star iteration.
                || m_util_s.re.is_loop(ex_app) // Handle loop.
            ) {
            SASSERT(ex_app->get_num_args() == 1);
            const auto child{ ex_app->get_arg(0) };
            SASSERT(is_app(child));
            extract_symbols(to_app(child), m_util_s, alphabet);
            return;
        } else if (m_util_s.re.is_range(ex_app)) { // Handle range.
            SASSERT(ex_app->get_num_args() == 2);
            const auto range_begin{ ex_app->get_arg(0) };
            const auto range_end{ ex_app->get_arg(1) };
            SASSERT(is_app(range_begin));
            SASSERT(is_app(range_end));
            const auto range_begin_value{ to_app(range_begin)->get_parameter(0).get_zstring()[0] };
            const auto range_end_value{ to_app(range_end)->get_parameter(0).get_zstring()[0] };

            auto current_value{ range_begin_value };
            while (current_value <= range_end_value) {
                alphabet.insert(current_value);
                ++current_value;
            }
        } else if (m_util_s.re.is_reverse(ex_app)) { // Handle reverse.
            util::throw_error("reverse is unsupported");
        } else if (m_util_s.re.is_union(ex_app)) { // Handle union (= or; A|B).
            SASSERT(ex_app->get_num_args() == 2);
            const auto left{ ex_app->get_arg(0) };
            const auto right{ ex_app->get_arg(1) };
            SASSERT(is_app(left));
            SASSERT(is_app(right));
            extract_symbols(to_app(left), m_util_s, alphabet);
            extract_symbols(to_app(right), m_util_s, alphabet);
            return;
        } else if(util::is_variable(ex_app)) { // Handle variable.
            util::throw_error("variable should not occur here");
        } else {
            // When ex is not string literal, variable, nor regex, recursively traverse the AST to find symbols.
            // TODO: maybe we can just leave is_range, is_variable and is_string in this function and otherwise do this:
            for(unsigned i = 0; i < ex_app->get_num_args(); i++) {
                SASSERT(is_app(ex_app->get_arg(i)));
                app *arg = to_app(ex_app->get_arg(i));
                extract_symbols(arg, m_util_s, alphabet);
            }
        }
    }

    [[nodiscard]] Nfa conv_to_nfa(app *expression, const seq_util& m_util_s, const ast_manager& m,
                                  const Alphabet& alphabet, bool determinize, bool make_complement) {

        if (m_util_s.str.is_string_term(expression)) {
            zstring result;
            if (m_util_s.str.is_string(expression, result)) {
                return AutAssignment::create_word_nfa(result);
            } else {
                util::throw_error("We can convert to NFA only string literals");
            }
        }

        SASSERT(m_util_s.is_re(expression));

        // to simulate recursive calls of conv_to_nfa on arguments of expression, we use postorder
        // traversal of the ast for expression
        std::stack<std::pair<app*, bool>> postorder_stack;
        postorder_stack.push({expression, false});
        std::stack<mata::nfa::Nfa> results_stack;
        std::map<app*, unsigned> num_of_regex_arguments;
        while (!postorder_stack.empty()) {
            auto [cur_expr, visited] = postorder_stack.top();
            postorder_stack.pop();

            if (!visited) { // we have not visited cur_expr -> we need to process children first
                postorder_stack.push({cur_expr, true});
                ptr_vector<expr> concatenation_args;
                if (!m_util_s.re.is_concat(cur_expr, concatenation_args)) {
                    for (size_t arg_idx = 0; arg_idx < cur_expr->get_num_args(); ++arg_idx) {
                        expr* arg = cur_expr->get_arg(arg_idx);
                        if (m_util_s.is_re(arg)) { // we only process childrens representing regexes
                            concatenation_args.push_back(arg);
                        }
                    }
                }
                num_of_regex_arguments[cur_expr] = concatenation_args.size();
                for (expr* arg : concatenation_args) {
                    SASSERT(is_app(arg));
                    postorder_stack.push({to_app(arg), false});
                }
            } else { // we already visited cur_expr -> the NFAs for its children should be on results_stack
                // we collect the NFAs for the children
                std::vector<mata::nfa::Nfa> arg_nfas;
                unsigned num_of_regex_arguments_of_cur_expr = num_of_regex_arguments.at(cur_expr);
                for (unsigned arg_idx = 0; arg_idx < num_of_regex_arguments_of_cur_expr; ++arg_idx) {
                    SASSERT(!results_stack.empty());
                    arg_nfas.push_back(std::move(results_stack.top()));
                    results_stack.pop();
                }

                STRACE("str-create_nfa",
                    tout << "--------------" << "Creating NFA for: " << mk_pp(const_cast<app*>(cur_expr), const_cast<ast_manager&>(m)) << "\n";
                );

                // create the resulting NFA for cur_expr
                Nfa result{};
                if (m_util_s.re.is_to_re(cur_expr)) { // Handle conversion of to regex function call.
                    SASSERT(cur_expr->get_num_args() == 1);
                    // Assume that expression inside re.to_re() function is a string of characters.
                    zstring arg_string;
                    if (!m_util_s.str.is_string(cur_expr->get_arg(0), arg_string)) { // if to_re has something other than string literal
                        util::throw_error("we support only string literals in str.to_re");
                    }
                    result = AutAssignment::create_word_nfa(arg_string);
                } else if (m_util_s.re.is_concat(cur_expr)) { // Handle regex concatenation.
                    SASSERT(num_of_regex_arguments_of_cur_expr > 0);
                    result = std::move(arg_nfas.at(0));
                    for (unsigned int i = 1; i < num_of_regex_arguments_of_cur_expr; ++i) {
                        result.concatenate(arg_nfas.at(i));
                        arg_nfas[i].clear();
                    }
                    result.trim();
                } else if (m_util_s.re.is_antimirov_union(cur_expr)) { // Handle Antimirov union.
                    util::throw_error("antimirov union is unsupported");
                } else if (m_util_s.re.is_complement(cur_expr)) { // Handle complement.
                    SASSERT(num_of_regex_arguments_of_cur_expr == 1);
                    result = std::move(arg_nfas.at(0));
                    if (cur_expr == expression) { // if we are processing root
                        // According to make_complement, we do complement at the end, so we just invert it
                        make_complement = !make_complement;
                    } else {
                        result = mata::nfa::complement(result, alphabet.mata_alphabet, {{"algorithm", "classical"}});
                    }
                } else if (m_util_s.re.is_derivative(cur_expr)) { // Handle derivative.
                    util::throw_error("derivative is unsupported");
                } else if (m_util_s.re.is_diff(cur_expr)) { // Handle diff.
                    util::throw_error("regex difference is unsupported");
                } else if (m_util_s.re.is_dot_plus(cur_expr)) { // Handle dot plus.
                    result.initial.insert(0);
                    result.final.insert(1);
                    for (const auto& symbol : alphabet.alphabet) {
                        result.delta.add(0, symbol, 1);
                        result.delta.add(1, symbol, 1);
                    }
                } else if (m_util_s.re.is_empty(cur_expr)) { // Handle empty language.
                    // Do nothing, as nfa is initialized empty
                } else if (m_util_s.re.is_epsilon(cur_expr)) { // Handle epsilon.
                    result = mata::nfa::builder::create_empty_string_nfa();
                } else if (m_util_s.re.is_full_char(cur_expr)) { // Handle full char (single occurrence of any string symbol, '.').
                    result.initial.insert(0);
                    result.final.insert(1);
                    for (const auto& symbol : alphabet.alphabet) {
                        result.delta.add(0, symbol, 1);
                    }
                } else if (m_util_s.re.is_full_seq(cur_expr)) {
                    result.initial.insert(0);
                    result.final.insert(0);
                    for (const auto& symbol : alphabet.alphabet) {
                        result.delta.add(0, symbol, 0);
                    }
                } else if (m_util_s.re.is_intersection(cur_expr)) { // Handle intersection.
                    SASSERT(num_of_regex_arguments_of_cur_expr > 0);
                    result = std::move(arg_nfas.at(0));
                    if (result.num_of_states() >= RED_BOUND) {
                        // first argument was not reduced if it is larger than RED_BOUND, however,
                        // intersection is expensive and it is (probably) better to reduce
                        // the arguments of intersection
                        result = mata::nfa::reduce(result);
                    }
                    for (unsigned int i = 1; i < num_of_regex_arguments_of_cur_expr; ++i) {
                        mata::nfa::Nfa next_arg = std::move(arg_nfas.at(i));
                        if (next_arg.num_of_states() >= RED_BOUND) {
                            // next_arg was not reduced if it is larger than RED_BOUND, however,
                            // intersection is expensive and it is (probably) better to reduce
                            // the arguments of intersection
                            next_arg = mata::nfa::reduce(next_arg);
                        }
                        result = mata::nfa::intersection(result, next_arg);
                    }
                } else if (m_util_s.re.is_loop(cur_expr)) { // Handle loop.
                    unsigned low, high;
                    expr *body;
                    bool is_high_set = false;
                    if (m_util_s.re.is_loop(cur_expr, body, low, high)) {
                        is_high_set = true;
                    } else if (m_util_s.re.is_loop(cur_expr, body, low)) {
                        is_high_set = false;
                    } else {
                        util::throw_error("loop should contain at least lower bound");
                    }

                    Nfa body_nfa = std::move(arg_nfas.at(0));

                    if (body_nfa.is_lang_empty()) {
                        // for the case that body of the loop represents empty language...
                        if (low == 0) {
                            // ...we either return empty string if we have \emptyset{0,h}
                            result = mata::nfa::builder::create_empty_string_nfa();
                        } else {
                            // ... or empty language
                            result = std::move(body_nfa);
                        }
                    } else if(body_nfa.is_universal(alphabet.mata_alphabet)) {
                        result = std::move(body_nfa);
                    } else {
                        body_nfa.unify_final();
                        body_nfa.unify_initial();

                        body_nfa = mata::nfa::reduce(body_nfa);
                        result = mata::nfa::builder::create_empty_string_nfa();
                    
                        if(low >= LOOP_BOUND) {
                            result = create_large_concat(body_nfa, low);
                        } else {
                            // we need to repeat body_nfa at least low times
                            for (unsigned i = 0; i < low; ++i) {
                                result.concatenate(body_nfa);
                                result.trim();
                            }
                        }

                        // we will now either repeat body_nfa high-low times (if is_high_set) or
                        // unlimited times (if it is not set), but we have to accept after each loop,
                        // so we add an empty word into body_nfa
                        mata::nfa::State new_state = body_nfa.add_state();
                        body_nfa.initial.insert(new_state);
                        body_nfa.final.insert(new_state);

                        body_nfa.unify_initial();
                        body_nfa = mata::nfa::reduce(body_nfa);

                        if (is_high_set) {
                            // if high is set, we repeat body_nfa another high-low times
                            for (unsigned i = 0; i < high - low; ++i) {
                                result.concatenate(body_nfa);
                                result.trim();
                            }
                        } else {
                            // if high is not set, we can repeat body_nfa unlimited more times
                            // so we do star operation on body_nfa and add it to end of nfa
                            for (const auto& final : body_nfa.final) {
                                for (const auto& initial : body_nfa.initial) {
                                    body_nfa.delta.add(final, mata::nfa::EPSILON, initial);
                                }
                            }
                            result = mata::nfa::concatenate(result, body_nfa, true);
                            result = mata::nfa::remove_epsilon(result);
                        }
                    }

                } else if (m_util_s.re.is_of_pred(cur_expr)) { // Handle of predicate.
                    util::throw_error("of predicate is unsupported");
                } else if (m_util_s.re.is_opt(cur_expr)) { // Handle optional.
                    SASSERT(num_of_regex_arguments_of_cur_expr == 1);
                    result = std::move(arg_nfas.at(0));
                    result.unify_initial();
                    for (const auto& initial : result.initial) {
                        result.final.insert(initial);
                    }
                } else if (m_util_s.re.is_range(cur_expr)) { // Handle range.
                    SASSERT(cur_expr->get_num_args() == 2);
                    const auto range_begin{ cur_expr->get_arg(0) };
                    const auto range_end{ cur_expr->get_arg(1) };
                    SASSERT(is_app(range_begin));
                    SASSERT(is_app(range_end));
                    const auto range_begin_value{ to_app(range_begin)->get_parameter(0).get_zstring()[0] };
                    const auto range_end_value{ to_app(range_end)->get_parameter(0).get_zstring()[0] };

                    result.initial.insert(0);
                    result.final.insert(1);
                    auto current_value{ range_begin_value };
                    while (current_value <= range_end_value) {
                        result.delta.add(0, current_value, 1);
                        ++current_value;
                    }
                } else if (m_util_s.re.is_reverse(cur_expr)) { // Handle reverse.
                    util::throw_error("reverse is unsupported");
                } else if (m_util_s.re.is_union(cur_expr)) { // Handle union (= or; A|B).
                    SASSERT(num_of_regex_arguments_of_cur_expr == 2);
                    result = std::move(arg_nfas.at(0));
                    result.unite_nondet_with(arg_nfas.at(1));
                } else if (m_util_s.re.is_star(cur_expr)) { // Handle star iteration.
                    SASSERT(num_of_regex_arguments_of_cur_expr == 1);
                    result = std::move(arg_nfas.at(0));
                    for (const auto& final : result.final) {
                        for (const auto& initial : result.initial) {
                            result.delta.add(final, mata::nfa::EPSILON, initial);
                        }
                    }
                    result.remove_epsilon();

                    // Make new initial final in order to accept empty string as is required by kleene-star.
                    mata::nfa::State new_state = result.add_state();
                    result.initial.insert(new_state);
                    result.final.insert(new_state);

                } else if (m_util_s.re.is_plus(cur_expr)) { // Handle positive iteration.
                    SASSERT(num_of_regex_arguments_of_cur_expr == 1);
                    result = std::move(arg_nfas.at(0));
                    for (const auto& final : result.final) {
                        for (const auto& initial : result.initial) {
                            result.delta.add(final, mata::nfa::EPSILON, initial);
                        }
                    }
                    result.remove_epsilon();
                } else if(util::is_variable(cur_expr)) { // Handle variable.
                    util::throw_error("variable in regexes are unsupported");
                } else {
                    util::throw_error("unsupported operation in regex");
                }

                // intermediate automata reduction
                // if the automaton is too big --> skip it. The computation of the simulation would be too expensive.
                if(result.num_of_states() < RED_BOUND) {
                    STRACE("str-create_nfa-reduce", 
                        tout << "--------------" << "NFA for: " << mk_pp(const_cast<app*>(cur_expr), const_cast<ast_manager&>(m)) << " that is going to be reduced" << "---------------" << std::endl;
                        tout << result;
                    );
                    result = mata::nfa::reduce(result);
                }

                STRACE("str-create_nfa",
                    tout << "--------------" << "NFA for: " << mk_pp(const_cast<app*>(cur_expr), const_cast<ast_manager&>(m)) << "---------------" << std::endl;
                    tout << result;
                );

                results_stack.push(std::move(result));
            }
        }

        SASSERT(results_stack.size() == 1);

        mata::nfa::Nfa final_result = std::move(results_stack.top());

        if(determinize && !make_complement) { // if we need to complement, we will determinize anyway
            STRACE("str-create_nfa-reduce", 
                tout << "--------------" << "NFA for: " << mk_pp(const_cast<app*>(expression), const_cast<ast_manager&>(m)) << " that is going to be minimized" << "---------------" << std::endl;
                tout << final_result;
            );
            final_result = mata::nfa::minimize(final_result);
        }

        // Whether to create complement of the final automaton.
        if (make_complement) {
            STRACE("str-create_nfa", tout << "Complemented NFA:" << std::endl;);
            final_result = mata::nfa::complement(final_result, alphabet.mata_alphabet, { 
                {"algorithm", "classical"}, 
                //{"minimize", "true"} // it seems that minimizing during complement causes more TOs in benchmarks
                });
        }

        STRACE("str-create_nfa", tout << final_result;);
        return final_result;
    }

    [[nodiscard]] RegexInfo get_regex_info(const app *expression, const seq_util& m_util_s) {
        if (m_util_s.re.is_to_re(expression)) { // Handle conversion of to regex function call.
            SASSERT(expression->get_num_args() == 1);
            const auto arg{ expression->get_arg(0) };
            // Assume that expression inside re.to_re() function is a string of characters.
            if (!m_util_s.str.is_string(arg)) { // if to_re has something other than string literal
                util::throw_error("we support only string literals in str.to_re");
            }
            return get_regex_info(to_app(arg), m_util_s);
        } else if (m_util_s.re.is_concat(expression)) { // Handle regex concatenation.
            SASSERT(expression->get_num_args() > 0);
            RegexInfo res = get_regex_info(to_app(expression->get_arg(0)), m_util_s);
            // min_length: sum of min_lengths of concats
            // empty: one of them is undef --> undef
            // universal: if min_length > 0 --> not universal
            for (unsigned int i = 1; i < expression->get_num_args(); ++i) {
                RegexInfo con = get_regex_info(to_app(expression->get_arg(i)), m_util_s);
                res.min_length += con.min_length;
                if(res.empty == l_undef || con.empty == l_undef) {
                    res.empty = l_undef;
                } else {
                    res.empty = to_lbool(res.empty == l_true || con.empty == l_true);
                }
            }
            
            if(res.min_length > 0) {
                res.universal = l_false;
            } else {
                res.universal = l_undef;
            }
            return res;
        } else if (m_util_s.re.is_antimirov_union(expression)) { // Handle Antimirov union.
            util::throw_error("antimirov union is unsupported");
        } else if (m_util_s.re.is_complement(expression)) { // Handle complement.
            SASSERT(expression->get_num_args() == 1);
            const auto child{ expression->get_arg(0) };
            SASSERT(is_app(child));
            // min_length: 0
            // empty: universal --> true; empty --> false; min_length > 0 and !empty --> false
            // universal: empty --> true< universal --> false
            RegexInfo res = get_regex_info(to_app(child), m_util_s);
            res.min_length = 0;
            if(res.empty == l_true) {
                res.empty = l_false;
                res.universal = l_true;
            } else if (res.min_length > 0 && res.empty == l_false) { // there is a word with length > 0
                res.universal = l_false;
                res.empty = l_false;
            } else if(res.universal == l_true) {
                res.universal = l_false;
                res.empty = l_true;
            } else {
                res.universal = l_undef;
                res.empty = l_undef;
            }
            return res;
        } else if (m_util_s.re.is_derivative(expression)) { // Handle derivative.
            util::throw_error("derivative is unsupported");
        } else if (m_util_s.re.is_diff(expression)) { // Handle diff.
            util::throw_error("regex difference is unsupported");
        } else if (m_util_s.re.is_dot_plus(expression)) { // Handle dot plus.
            return RegexInfo{.min_length = 1, .universal = l_false, .empty = l_false};
        } else if (m_util_s.re.is_empty(expression)) { // Handle empty language.
            return RegexInfo{.min_length = 0, .universal = l_false, .empty = l_true};
        } else if (m_util_s.re.is_epsilon(expression)) { // Handle epsilon.
            return RegexInfo{.min_length = 0, .universal = l_false, .empty = l_false};
        } else if (m_util_s.re.is_full_char(expression)) { // Handle full char (single occurrence of any string symbol, '.').
            return RegexInfo{.min_length = 1, .universal = l_false, .empty = l_false};
        } else if (m_util_s.re.is_full_seq(expression)) {
            return RegexInfo{.min_length = 0, .universal = l_true, .empty = l_false};
        } else if (m_util_s.re.is_intersection(expression)) { // Handle intersection.
            SASSERT(expression->get_num_args() > 0);
            // min_length: maximum of each regex from intersection
            // empty: if one of them is empty --> true; otherwise undef
            // universal: min_length > 0 --> false; otherwise undef
            RegexInfo res = get_regex_info(to_app(expression->get_arg(0)), m_util_s);
            for (unsigned int i = 1; i < expression->get_num_args(); ++i) {
                RegexInfo prod = get_regex_info(to_app(expression->get_arg(i)), m_util_s);
                res.min_length = std::max(res.min_length, prod.min_length);
                if(prod.empty == l_true) {
                    res.empty = l_true;
                }
            }
            if(res.empty != l_true) {
                res.empty =  l_undef;
            }
            res.universal = l_undef;
            if(res.min_length > 0) {
                res.universal = l_false;
            }
            return res;
        } else if (m_util_s.re.is_loop(expression)) { // Handle loop.
            unsigned low, high;
            expr *body;
            if (m_util_s.re.is_loop(expression, body, low, high)) {
            } else if (m_util_s.re.is_loop(expression, body, low)) {
            } else {
                util::throw_error("loop should contain at least lower bound");
            }

            // min_length: low == 0 --> 0; otherwise min_length * low
            // empty: low == 0 --> false; otherwise the same as the original empty
            // universal: min_length > 0 --> false; empty && low == 0 --> false
            RegexInfo res = get_regex_info(to_app(body), m_util_s);
            if(res.empty == l_true && low == 0) {
                return RegexInfo{.min_length = 0, .universal = l_false, .empty = l_false};
            }
            res.min_length *= low;
            if(res.min_length > 0) {
                res.universal = l_false;
            }
            return res;

        } else if (m_util_s.re.is_of_pred(expression)) { // Handle of predicate.
            util::throw_error("of predicate is unsupported");
        } else if (m_util_s.re.is_opt(expression)) { // Handle optional.
            SASSERT(expression->get_num_args() == 1);
            const auto child{ expression->get_arg(0) };
            SASSERT(is_app(child));
            // min_length: 0 (epsilon)
            RegexInfo res = get_regex_info(to_app(child), m_util_s);
            res.min_length = 0;
            res.empty = l_false;
            return res;
        } else if (m_util_s.re.is_range(expression)) { // Handle range.
            SASSERT(expression->get_num_args() == 2);
            const auto range_begin{ expression->get_arg(0) };
            const auto range_end{ expression->get_arg(1) };
            SASSERT(is_app(range_begin));
            SASSERT(is_app(range_end));
            const auto range_begin_value{ to_app(range_begin)->get_parameter(0).get_zstring()[0] };
            const auto range_end_value{ to_app(range_end)->get_parameter(0).get_zstring()[0] };

            // min_length: if there is some symbol in range --> min_length = 1; otherwise min_length = 0 (empty)
            // empty:  if there is some symbol in range --> false; otherwise true
            // universal: false
            if(range_begin_value <= range_end_value) {
                return RegexInfo{.min_length = 1, .universal = l_false, .empty = l_false};
            } else {
                return RegexInfo{.min_length = 0, .universal = l_false, .empty = l_true};
            }
        } else if (m_util_s.re.is_reverse(expression)) { // Handle reverse.
            util::throw_error("reverse is unsupported");
        } else if (m_util_s.re.is_union(expression)) { // Handle union (= or; A|B).
            SASSERT(expression->get_num_args() == 2);
            const auto left{ expression->get_arg(0) };
            const auto right{ expression->get_arg(1) };
            SASSERT(is_app(left));
            SASSERT(is_app(right));
            
            // min_length: minimum of min_length of both guys
            // empty: if one of them is not empty --> false; otherwise undef
            // universal: if min_length > 0 --> false; if both are universal --> true; otherwise undef
            RegexInfo res = get_regex_info(to_app(left), m_util_s);
            RegexInfo uni = get_regex_info(to_app(right), m_util_s);
            res.min_length = std::min(uni.min_length, res.min_length);
            if(uni.empty == l_false || res.empty == l_false) {
                res.empty = l_false;
            } else if(res.empty == l_true && uni.empty == l_true) {
                res.empty = l_true;
            } else {
                res.empty = l_undef;
            }
            if(res.universal == l_true || uni.universal == l_true) {
                res.universal = l_true;
            } else {
                res.universal = l_undef;
            }

            if(res.min_length > 0) {
                res.universal = l_false;
            }
            return res;
            
        } else if (m_util_s.re.is_star(expression)) { // Handle star iteration.
            SASSERT(expression->get_num_args() == 1);
            const auto child{ expression->get_arg(0) };
            SASSERT(is_app(child));
            RegexInfo res = get_regex_info(to_app(child), m_util_s);
            return RegexInfo{.min_length = 0, .universal = res.universal == l_true ? l_true : l_undef, .empty = l_false};

        } else if (m_util_s.re.is_plus(expression)) { // Handle positive iteration.
            SASSERT(expression->get_num_args() == 1);
            const auto child{ expression->get_arg(0) };
            SASSERT(is_app(child));

            // empty: the original guy is empty <--> true
            RegexInfo res = get_regex_info(to_app(child), m_util_s);
            res.universal = l_undef;
            return res;
        } else if(m_util_s.str.is_string(expression)) { // Handle string literal.
            SASSERT(expression->get_num_parameters() == 1);
            return RegexInfo{.min_length = expression->get_parameter(0).get_zstring().length(), .universal = l_false, .empty = l_false};
        } else if(util::is_variable(expression)) { // Handle variable.
            util::throw_error("variable in regexes are unsupported");
        } else {
            util::throw_error("unsupported operation in regex");
        }
        return RegexInfo{.min_length = 0, .universal = l_undef, .empty = l_undef};
    }

    mata::nfa::Nfa create_large_concat(const mata::nfa::Nfa& body_nfa, unsigned count) {
        mata::nfa::Nfa nfa_part = mata::nfa::builder::create_empty_string_nfa();
        mata::nfa::Nfa nfa = mata::nfa::builder::create_empty_string_nfa();
        const unsigned CONCAT = 100;

        for(unsigned i = 0; i < CONCAT; i++) {
            nfa_part.concatenate(body_nfa);
            nfa_part.trim();
        }
        unsigned cnt = 0;
        for(unsigned i = 0; i < count / CONCAT; i++) {
            nfa.concatenate(nfa_part);
            nfa.trim();
            cnt += CONCAT;
        }
        for(; cnt <= count; cnt++) {
            nfa.concatenate(body_nfa);
            nfa.trim();
        }

        return nfa;
    }

    unsigned get_loop_sum(const app* reg, const seq_util& m_util_s) {
        expr* body;
        unsigned lo, hi;
        if (m_util_s.re.is_loop(reg, body, lo, hi)) {
            unsigned body_loop = get_loop_sum(to_app(body), m_util_s);
            if (body_loop == 0) {
                return hi;
            } else {
                return hi*body_loop;
            }
        } else if (m_util_s.str.is_string(reg)) {
            return 0;
        } else {
            unsigned sum = 0;
            for (unsigned arg_num = 0; arg_num < reg->get_num_args(); ++arg_num) {
                sum += get_loop_sum(to_app(reg->get_arg(arg_num)), m_util_s);
            }
            return sum;
        }
    }

    zstring get_model_from_regex(const app *regex, const seq_util& m_util_s) {
        if (m_util_s.re.is_to_re(regex)) { // Handle conversion of to regex function call.
            SASSERT(regex->get_num_args() == 1);
            const auto arg{ regex->get_arg(0) };
            // Assume that regex inside re.to_re() function is a string of characters.
            if (!m_util_s.str.is_string(arg)) { // if to_re has something other than string literal
                throw regex_model_fail();
            }
            return get_model_from_regex(to_app(arg), m_util_s);
        } else if (m_util_s.re.is_concat(regex)) { // Handle regex concatenation.
            SASSERT(regex->get_num_args() > 0);
            zstring result;
            for (unsigned int i = 0; i < regex->get_num_args(); ++i) {
                result = result + get_model_from_regex(to_app(regex->get_arg(i)), m_util_s);
            }
            return result;
        } else if (m_util_s.re.is_complement(regex)) { // Handle complement.
            SASSERT(regex->get_num_args() == 1);
            throw regex_model_fail();
        } else if (m_util_s.re.is_diff(regex)) { // Handle diff.
            throw regex_model_fail();
        } else if (m_util_s.re.is_dot_plus(regex)) { // Handle dot plus.
            return zstring("a"); // return one iteration, i.e., arbitrary char
        } else if (m_util_s.re.is_empty(regex)) { // Handle empty language.
            throw regex_model_fail();
        } else if (m_util_s.re.is_epsilon(regex)) { // Handle epsilon.
            return zstring();
        } else if (m_util_s.re.is_full_char(regex)) { // Handle full char (single occurrence of any string symbol, '.').
            return zstring("a"); // return arbitrary char
        } else if (m_util_s.re.is_full_seq(regex)) {
            return zstring(); // return arbitrary word
        } else if (m_util_s.re.is_intersection(regex)) { // Handle intersection.
            SASSERT(regex->get_num_args() > 0);
            // TODO we could possibly handle this by creating automata, their intersection and returning their model
            throw regex_model_fail();
        } else if (m_util_s.re.is_loop(regex)) { // Handle loop.
            unsigned low, high;
            expr *body;
            VERIFY(m_util_s.re.is_loop(regex, body, low, high) || m_util_s.re.is_loop(regex, body, low));

            // return model from body iterated low times
            if (low == 0 || low > high) {
                return zstring();
            } else {
                const zstring inside = get_model_from_regex(to_app(body), m_util_s);
                std::vector<unsigned> result; // to make it more effecient, we use vector instead of zstring, using only zstring concatenation was very slow
                result.reserve(inside.length()*low);
                for (unsigned i = 0; i < low; ++i) {
                    for (unsigned j = 0; j < inside.length(); ++j) {
                        result.push_back(inside[j]);
                    }
                }
                return zstring(result.size(), result.data());
            }
        } else if (m_util_s.re.is_opt(regex)) { // Handle optional.
            return zstring(); // we can ignore inside and just return empty string, 
        } else if (m_util_s.re.is_range(regex)) { // Handle range.
            SASSERT(regex->get_num_args() == 2);
            const auto range_begin{ regex->get_arg(0) };
            const auto range_end{ regex->get_arg(1) };
            SASSERT(is_app(range_begin));
            SASSERT(is_app(range_end));
            const auto range_begin_value{ to_app(range_begin)->get_parameter(0).get_zstring()[0] };
            const auto range_end_value{ to_app(range_end)->get_parameter(0).get_zstring()[0] };
            if (range_begin_value > range_end_value) {
                return zstring(); // if range is invalid, it means empty string
            } else {
                return to_app(range_begin)->get_parameter(0).get_zstring(); // otherwise, we return the start of the range
            }
        } else if (m_util_s.re.is_union(regex)) { // Handle union (= or; A|B).
            SASSERT(regex->get_num_args() == 2);
            const auto left{ regex->get_arg(0) };
            SASSERT(is_app(left));
            const auto right{ regex->get_arg(1) };
            SASSERT(is_app(right));
            // try getting a model from left, if it is not possible, then try right
            try {
                return regex::get_model_from_regex(to_app(left), m_util_s);
            } catch (const regex::regex_model_fail& exc) {
                return regex::get_model_from_regex(to_app(right), m_util_s);
            }
        } else if (m_util_s.re.is_star(regex)) { // Handle star iteration.
            return zstring(); // empty string is always accepted by star
        } else if (m_util_s.re.is_plus(regex)) { // Handle positive iteration.
            SASSERT(regex->get_num_args() == 1);
            const auto child{ regex->get_arg(0) };
            SASSERT(is_app(child));
            return get_model_from_regex(to_app(child), m_util_s); // we just return one iteration
        } else if (m_util_s.str.is_string(regex)) { // Handle string literal.
            SASSERT(regex->get_num_parameters() == 1);
            return regex->get_parameter(0).get_zstring();
        } else {
            throw regex_model_fail();
        }
    }

    bool ReplaceAllPrefixTree::add_find(const zstring& find, const zstring& replace) {
        if (find.length() == 0 || find_prefixes.contains(find)) {
            return false;
        }
        for (unsigned find_char : find) {
            if (replace_chars.contains(find_char)) {
                return false;
            }
        }

        zstring prefix;
        mata::nfa::State cur_state = 0;
        for (unsigned find_char : find) {
            prefix = prefix + find_char;
            find_prefixes.insert(prefix);
            auto next_state_it = prefix_automaton.delta[cur_state].find(find_char);
            if (next_state_it != prefix_automaton.delta[cur_state].end()) {
                SASSERT(next_state_it->targets.size() == 1);
                cur_state = next_state_it->targets.front();
            } else {
                mata::nfa::State next_state = prefix_automaton.add_state();
                prefix_automaton.delta.add(cur_state, find_char, next_state);
                cur_state = next_state;
            }
        }
        prefix_automaton.final.insert(cur_state);
        replacing_map[cur_state] = util::get_mata_word_zstring(replace);

        for (unsigned replace_char : replace) {
            replace_chars.insert(replace_char);
        }


        return true;
    }

    mata::nft::Nft ReplaceAllPrefixTree::create_transducer(mata::Alphabet* mata_alph) {
        mata::nft::Nft result{1, {0}, {0}};
        std::queue<std::tuple<mata::Word,mata::nfa::State,mata::nft::State>> worklist;
        worklist.push({mata::Word(), 0, 0});

        while (!worklist.empty()) {
            auto [word, prefix_state, result_state] = worklist.front();
            worklist.pop();
            for (mata::Symbol symbol : mata_alph->get_alphabet_symbols()) {
                mata::Word next_word = word;
                next_word.push_back(symbol);
                auto symbol_transition_it = prefix_automaton.delta[prefix_state].find(symbol);
                if (symbol_transition_it != prefix_automaton.delta[prefix_state].end()) {
                    SASSERT(symbol_transition_it->targets.size() == 1);
                    mata::nfa::State next_prefix_state = symbol_transition_it->targets.front();
                    if (prefix_automaton.final[next_prefix_state]) {
                        mata::Word replacing_word = replacing_map[next_prefix_state];
                        mata::nft::State next_state = result.add_transition(result_state, {symbol, replacing_word[0]});
                        for (size_t i = 1; i < replacing_word.size()-1; ++i) {
                            next_state = result.add_transition(next_state, {mata::nft::EPSILON, replacing_word[i]});
                        }
                        result.add_transition(next_state, {mata::nft::EPSILON, replacing_word[replacing_word.size()-1]}, 0);
                    } else {
                        mata::nft::State next_result_state = result.add_transition(result_state, {symbol, mata::nft::EPSILON});
                        worklist.push({next_word, next_prefix_state, next_result_state});
                    }
                } else {
                    mata::nft::State next_state = result.add_transition(result_state, {symbol, next_word[0]});
                    for (size_t i = 1; i < next_word.size()-1; ++i) {
                        next_state = result.add_transition(next_state, {mata::nft::EPSILON, next_word[i]});
                    }
                    result.add_transition(next_state, {mata::nft::EPSILON, next_word[next_word.size()-1]}, 0);
                }
            }
        }
        return result;
    }

    void gather_transducer_constraints(app* ex, ast_manager& m, const seq_util& m_util_s, obj_map<expr, expr*>& pred_replace, std::map<BasicTerm, expr_ref>& var_name, mata::Alphabet* mata_alph, std::vector<Predicate>& transducer_preds) {
        if (m_util_s.str.is_string(ex) || util::is_variable(ex)) { // Handle string literals.
            return;
        }

        expr * a1 = nullptr, *a2 = nullptr, *a3 = nullptr;

        if (m_util_s.str.is_concat(ex, a1, a2)) {
            gather_transducer_constraints(to_app(a1), m, m_util_s, pred_replace, var_name, mata_alph, transducer_preds);
            gather_transducer_constraints(to_app(a2), m, m_util_s, pred_replace, var_name, mata_alph, transducer_preds);
            return;
        }

        expr* rpl = pred_replace.find(ex); // dies if it is not found

        // collect all nested replace_all and replace_re_all and keep their arguments as pairs
        // in find_and_replace (where find can be either zstring for replace_all or NFA for 
        // replace_re_all)
        std::vector<std::pair<std::variant<zstring,mata::nfa::Nfa>,zstring>> find_and_replace;
        while (true) {
            if (m_util_s.str.is_replace_all(ex, a1, a2, a3)) {
                zstring find, replace;
                if(!m_util_s.str.is_string(a2, find) || !m_util_s.str.is_string(a3, replace)) {
                    util::throw_error("only replace_all with concrete find&replace is supported");
                }

                find_and_replace.emplace_back(find, replace);
                ex = to_app(a1);
            } else if (m_util_s.str.is_replace_re_all(ex, a1, a2, a3)) {
                zstring replace;
                if(!m_util_s.str.is_string(a3, replace)) {
                    util::throw_error("only replace_re_all with concrete find&replace is supported");
                }

                // construct NFA corresponding to the regex find
                auto ov = mata_alph->get_alphabet_symbols();
                std::set<mata::Symbol> syms(ov.begin(), ov.end());
                Alphabet alph(syms);
                mata::nfa::Nfa find_nfa = conv_to_nfa(to_app(a2), m_util_s, m, alph);

                find_and_replace.emplace_back(find_nfa, replace);
                ex = to_app(a1);
            } else {
                break;
            }
        }

        if (!find_and_replace.empty()) {
            // recursively call on nested parameters
            gather_transducer_constraints(ex, m, m_util_s, pred_replace, var_name, mata_alph, transducer_preds);
            // collect and replace replace_(re)_all argument with a concatenation of basic terms
            std::vector<BasicTerm> side {};
            util::collect_terms(ex, m, m_util_s, pred_replace, var_name, side);

            // result of the replace_all
            std::string var_name = to_app(rpl)->get_decl()->get_name().str();
            BasicTerm result_var(BasicTermType::Variable, var_name);


            // iterate backwards and construct transducer representing the replace operations
            auto backward_iterator = find_and_replace.rbegin();
            auto backward_iterator_end = find_and_replace.rend();
            auto get_next_transducer = [&mata_alph,&backward_iterator,&backward_iterator_end]() {
                auto backward_iterator_old = backward_iterator;
                auto& find = backward_iterator->first;
                zstring& replace = backward_iterator->second;
                ReplaceAllPrefixTree prefix_tree;
                while (backward_iterator != backward_iterator_end && std::holds_alternative<zstring>(backward_iterator->first)) {
                    if (prefix_tree.add_find(std::get<zstring>(find), replace)) {
                        ++backward_iterator;
                    }
                }

                if (backward_iterator != backward_iterator_old) {
                    return prefix_tree.create_transducer(mata_alph);
                } else {
                    SASSERT(backward_iterator != backward_iterator_end);
                    mata::nft::Nft result = std::holds_alternative<zstring>(find) ?
                                                mata::nft::strings::replace_reluctant_literal(util::get_mata_word_zstring(std::get<zstring>(find)), util::get_mata_word_zstring(replace), mata_alph)
                                              : mata::nft::strings::replace_reluctant_regex(std::get<mata::nfa::Nfa>(find), util::get_mata_word_zstring(replace), mata_alph);
                    ++backward_iterator;
                    return mata::nft::reduce(mata::nft::remove_epsilon(result).trim()).trim();
                }
            };

            mata::nft::Nft transducer = get_next_transducer();
            while (backward_iterator != backward_iterator_end) {
                transducer = mata::nft::compose(transducer, get_next_transducer(), 1, 0);
                transducer = mata::nft::reduce(mata::nft::remove_epsilon(transducer).trim()).trim();
            }

            transducer_preds.push_back(Predicate::create_transducer(std::make_shared<mata::nft::Nft>(transducer), side, {result_var}));
            return;
        }
    }

}
