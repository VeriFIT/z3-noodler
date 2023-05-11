#include <cassert>
#include <mata/re2parser.hh>

#include "util.h"
#include "theory_str_noodler.h"
#include "inclusion_graph.h"
#include "aut_assignment.h"
#include "util/z3_exception.h"

namespace {
    using Mata::Nfa::Nfa;
}

namespace smt::noodler::util {

    void throw_error(std::string errMsg) {
#ifndef NDEBUG
        // for debugging, we use std::runtime_error, because that one is not caught by z3
        throw std::runtime_error(errMsg);
#else
        // for release, we use this, as it is caught by z3 and it transform it into 'unknown'
        throw default_exception(std::move(errMsg));
#endif
    }

    void extract_symbols(expr* const ex, const seq_util& m_util_s, const ast_manager& m, std::set<uint32_t>& alphabet) {
        if (m_util_s.str.is_string(ex)) {
            auto ex_app{ to_app(ex) };
            SASSERT(ex_app->get_num_parameters() == 1);
            const zstring string_literal{ zstring{ ex_app->get_parameter(0).get_zstring() } };
            for (size_t i{ 0 }; i < string_literal.length(); ++i) {
                alphabet.insert(string_literal[i]);
            }
            return;
        }

        if(util::is_variable(ex, m_util_s)) { // Skip variables.
            return;
        }

        SASSERT(is_app(ex));
        app* ex_app = to_app(ex);

        if (m_util_s.re.is_to_re(ex_app)) { // Handle conversion to regex function call.
            SASSERT(ex_app->get_num_args() == 1);
            const auto arg{ ex_app->get_arg(0) };
            // Assume that expression inside re.to_re() function is a string of characters.
            if (!m_util_s.str.is_string(arg)) { // if to_re has something other than string literal
                throw_error("we support only string literals in str.to_re");
            }
            extract_symbols(to_app(arg), m_util_s, m, alphabet);
            return;
        } else if (m_util_s.re.is_concat(ex_app) // Handle regex concatenation.
                || m_util_s.str.is_concat(ex_app) // Handle string concatenation.
                || m_util_s.re.is_intersection(ex_app) // Handle intersection.
            ) {
            for (unsigned int i = 0; i < ex_app->get_num_args(); ++i) {
                extract_symbols(to_app(ex_app->get_arg(i)), m_util_s, m, alphabet);
            }
            return;
        } else if (m_util_s.re.is_antimirov_union(ex_app)) { // Handle Antimirov union.
            throw_error("antimirov union is unsupported");
        } else if (m_util_s.re.is_complement(ex_app)) { // Handle complement.
            SASSERT(ex_app->get_num_args() == 1);
            const auto child{ ex_app->get_arg(0) };
            SASSERT(is_app(child));
            extract_symbols(to_app(child), m_util_s, m, alphabet);
            return;
        } else if (m_util_s.re.is_derivative(ex_app)) { // Handle derivative.
            throw_error("derivative is unsupported");
        } else if (m_util_s.re.is_diff(ex_app)) { // Handle diff.
            throw_error("regex difference is unsupported");
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
            throw_error("of predicate is unsupported");
        } else if (m_util_s.re.is_opt(ex_app) // Handle optional.
                || m_util_s.re.is_plus(ex_app) // Handle positive iteration.
                || m_util_s.re.is_star(ex_app) // Handle star iteration.
                || m_util_s.re.is_loop(ex_app) // Handle loop.
            ) {
            SASSERT(ex_app->get_num_args() == 1);
            const auto child{ ex_app->get_arg(0) };
            SASSERT(is_app(child));
            extract_symbols(to_app(child), m_util_s, m, alphabet);
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
            throw_error("reverse is unsupported");
        } else if (m_util_s.re.is_union(ex_app)) { // Handle union (= or; A|B).
            SASSERT(ex_app->get_num_args() == 2);
            const auto left{ ex_app->get_arg(0) };
            const auto right{ ex_app->get_arg(1) };
            SASSERT(is_app(left));
            SASSERT(is_app(right));
            extract_symbols(to_app(left), m_util_s, m, alphabet);
            extract_symbols(to_app(right), m_util_s, m, alphabet);
            return;
        } else if(is_variable(ex_app, m_util_s)) { // Handle variable.
            throw_error("variable should not occur here");
        } else {
            // When ex is not string literal, variable, nor regex, recursively traverse the AST to find symbols.
            // TODO: maybe we can just leave is_range, is_variable and is_string in this function and otherwise do this:
            for(unsigned i = 0; i < ex_app->get_num_args(); i++) {
                SASSERT(is_app(ex_app->get_arg(i)));
                app *arg = to_app(ex_app->get_arg(i));
                extract_symbols(arg, m_util_s, m, alphabet);
            }
        }
    }

    void get_str_variables(expr* const ex, const seq_util& m_util_s, const ast_manager& m, obj_hashtable<expr>& res, obj_map<expr, expr*>* pred_map) {
        if(m_util_s.str.is_string(ex)) {
            return;
        }

        if(is_str_variable(ex, m_util_s)) {
            res.insert(ex);
            return;
        }

        SASSERT(is_app(ex));
        app* ex_app{ to_app(ex) };
        if(pred_map != nullptr) {
            expr* rpl;
            if(pred_map->find(ex_app, rpl)) {
                get_str_variables(rpl, m_util_s, m, res, pred_map);
            }
        }

        for(unsigned i = 0; i < ex_app->get_num_args(); i++) {
            SASSERT(is_app(ex_app->get_arg(i)));
            app *arg = to_app(ex_app->get_arg(i));
            get_str_variables(arg, m_util_s, m, res, pred_map);
        }
    }

    void get_variable_names(expr* const ex, const seq_util& m_util_s, const ast_manager& m, std::unordered_set<std::string>& res) {
        if(m_util_s.str.is_string(ex)) {
            return;
        }

        if(is_variable(ex, m_util_s)) {
            res.insert(std::to_string(to_app(ex)->get_name()));
            return;
        }

        SASSERT(is_app(ex));
        app* ex_app{ to_app(ex) };

        for(unsigned i = 0; i < ex_app->get_num_args(); i++) {
            SASSERT(is_app(ex_app->get_arg(i)));
            app *arg = to_app(ex_app->get_arg(i));
            get_variable_names(arg, m_util_s, m, res);
        }
    }

    bool is_variable(const expr* expression, const seq_util& m_util_s) {
        // TODO: When we are able to detect other kinds of variables, add their checks here.
        return is_str_variable(expression, m_util_s);
    }

    bool is_str_variable(const expr* expression, const seq_util& m_util_s) {
        if(m_util_s.str.is_string(expression)) { // Filter away string literals first.
            return false;
        }

        // TODO: we are not sure if this is correct, we just hope
        if (m_util_s.is_string(expression->get_sort()) &&
            is_app(expression) && to_app(expression)->get_num_args() == 0) {
            return true;
        }

        return false;
    }

    std::set<uint32_t> get_dummy_symbols(size_t new_symb_num, std::set<uint32_t>& symbols_to_append_to) {
        std::set<uint32_t> dummy_symbols{};
        uint32_t dummy_symbol{ 0 };
        const size_t disequations_number{ new_symb_num };
        for (size_t diseq_index{ 0 }; diseq_index < disequations_number; ++diseq_index) {
            while (symbols_to_append_to.find(dummy_symbol) != symbols_to_append_to.end()) { ++dummy_symbol; }
            dummy_symbols.insert(dummy_symbol);
            ++dummy_symbol;
        }
        [[maybe_unused]] const size_t dummy_symbols_number{ dummy_symbols.size() };
        assert(dummy_symbols_number == disequations_number);
        [[maybe_unused]] const size_t symbols_in_formula_number{ symbols_to_append_to.size() };
        symbols_to_append_to.insert(dummy_symbols.begin(), dummy_symbols.end());
        assert(dummy_symbols_number + symbols_in_formula_number == symbols_to_append_to.size());
        return dummy_symbols;
    }

    std::set<uint32_t> get_symbols_for_formula(
            const vector<expr_pair>& equations,
            const vector<expr_pair>& disequations,
            const vector<expr_pair_flag>& regexes,
            const vector<expr_pair_flag>& lang_regexes,
            const seq_util& m_util_s,
            const ast_manager& m
    ) {
        std::set<uint32_t> symbols_in_formula{};
        for (const auto &word_equation: equations) {
            util::extract_symbols(word_equation.first, m_util_s, m, symbols_in_formula);
            util::extract_symbols(word_equation.second, m_util_s, m, symbols_in_formula);
        }

        for (const auto &word_equation: disequations) {
            util::extract_symbols(word_equation.first, m_util_s, m, symbols_in_formula);
            util::extract_symbols(word_equation.second, m_util_s, m, symbols_in_formula);
        }

        for (const auto &word_equation: regexes) {
            util::extract_symbols(std::get<1>(word_equation), m_util_s, m, symbols_in_formula);
        }

        for (const auto &lang_eq: lang_regexes) {
            util::extract_symbols(std::get<0>(lang_eq), m_util_s, m, symbols_in_formula);
            util::extract_symbols(std::get<1>(lang_eq), m_util_s, m, symbols_in_formula);
        }
        return symbols_in_formula;
    }

    AutAssignment create_aut_assignment_for_formula(
            const Formula& instance,
            const vector<expr_pair_flag>& regexes,
            std::map<BasicTerm, expr_ref>& var_name,
            const seq_util& m_util_s,
            const ast_manager& m,
            const std::set<uint32_t>& noodler_alphabet
    ) {
        // Find all variables in the whole formula.
        std::unordered_set<BasicTerm> variables_in_formula{};

        for (const auto &pred: instance.get_predicates()) {
            auto vars = pred.get_vars();
            variables_in_formula.insert(vars.begin(), vars.end());
        }

        AutAssignment aut_assignment{};
        aut_assignment.set_alphabet(noodler_alphabet);
        // Create automata from their corresponding regexes.
        std::unordered_set<std::string> variables_with_regex{};
        for (const auto &word_equation: regexes) {
            const auto& variable{ std::get<0>(word_equation) };
            assert(is_app(variable));
            const auto& variable_app{ to_app(variable) };
            assert(variable_app->get_num_args() == 0);
            const auto& variable_name{ variable_app->get_decl()->get_name().str() };
            variables_with_regex.insert(variable_name);
            const BasicTerm variable_term{ BasicTermType::Variable, variable_name };
            // If the regular constraint is in a negative form, create a complement of the regular expression instead.
            const bool make_complement{ !std::get<2>(word_equation) };
            Nfa nfa{ conv_to_nfa(to_app(std::get<1>(word_equation)), m_util_s, m, noodler_alphabet, make_complement) };
            auto aut_ass_it{ aut_assignment.find(variable_term) };
            if (aut_ass_it != aut_assignment.end()) {
                // This variable already has some regular constraints. Hence, we create an intersection of the new one
                //  with the previously existing.
                aut_ass_it->second = std::make_shared<Nfa>(
                        Mata::Nfa::intersection(nfa, *aut_ass_it->second));
            } else { // We create a regular constraint for the current variable for the first time.
                aut_assignment[variable_term] = std::make_shared<Nfa>(std::forward<Nfa>(std::move(nfa)));
                var_name.insert({variable_term, variable});
            }
        }

        // Assign sigma start automata for all yet unassigned variables.
        Mata::OnTheFlyAlphabet* mata_alphabet{ new Mata::OnTheFlyAlphabet{} };
        std::string hex_symbol_string;
        for (const uint32_t symbol : noodler_alphabet) {
            mata_alphabet->add_new_symbol(std::to_string(symbol), symbol);
        }

        const Nfa nfa_sigma_star{ Mata::Nfa::create_sigma_star_nfa(mata_alphabet) };
        for (const auto& variable : variables_in_formula) {
            if (variables_with_regex.find(variable.get_name().encode()) == variables_with_regex.end()) {
                assert(aut_assignment.find(variable) == aut_assignment.end());
                aut_assignment[variable] = std::make_shared<Nfa>(nfa_sigma_star);
            }
        }

        STRACE("str-nfa",
            tout << "Created automata assignment for formula:" << std::endl;
            for (const auto& single_aut_assignment: aut_assignment) {
               tout << single_aut_assignment.first.get_name() << std::endl;
               single_aut_assignment.second->print_to_DOT(tout);
            }
        );

        return aut_assignment;
    }

    std::string conv_to_regex_hex(const app *expr, const seq_util& m_util_s, const ast_manager& m, const std::set<uint32_t>& alphabet) {
        std::string regex{};
        if (m_util_s.re.is_to_re(expr)) { // Handle conversion to regex function call.
            // Assume that expression inside re.to_re() function is a string of characters.
            SASSERT(expr->get_num_args() == 1);
            const auto arg{ expr->get_arg(0) };
            regex = conv_to_regex_hex(to_app(arg), m_util_s, m, alphabet);
        } else if (m_util_s.re.is_concat(expr)) { // Handle concatenation.
            SASSERT(expr->get_num_args() == 2);
            const auto left{ expr->get_arg(0) };
            const auto right{ expr->get_arg(1) };
            SASSERT(is_app(left));
            SASSERT(is_app(right));
            regex = conv_to_regex_hex(to_app(left), m_util_s, m, alphabet) + conv_to_regex_hex(to_app(right), m_util_s, m, alphabet);
        } else if (m_util_s.re.is_antimirov_union(expr)) { // Handle Antimirov union.
            assert(false && "re.is_antimirov_union(expr)");
        } else if (m_util_s.re.is_complement(expr)) { // Handle complement.
            assert(false && "re.is_complement(expr)");
        } else if (m_util_s.re.is_derivative(expr)) { // Handle derivative.
            assert(false && "re.is_derivative(expr)");
        } else if (m_util_s.re.is_diff(expr)) { // Handle diff.
            assert(false && "re.is_diff(expr)");
        } else if (m_util_s.re.is_dot_plus(expr)) { // Handle dot plus.
            assert(false && "re.is_dot_plus(expr)");
        } else if (m_util_s.re.is_empty(expr)) { // Handle empty string.
            assert(false && "re.is_empty(expr)");
        } else if (m_util_s.re.is_epsilon(expr)) { // Handle epsilon.
            assert(false && "re.is_epsilon(expr)");
        } else if (m_util_s.re.is_full_char(expr)) { // Handle full char (single occurrence of any string symbol, '.').
            regex += "[";
            std::stringstream convert_stream;
            for (const auto& symbol : alphabet) {
                convert_stream << std::dec << "\\x{" << std::hex << symbol << std::dec << "}";
            }
            regex += convert_stream.str();
            regex += "]";
        } else if (m_util_s.re.is_full_seq(expr)) {
            // Handle full sequence of characters (any sequence of characters, '.*') (SMT2: re.all).

            regex += "[";
            std::stringstream convert_stream;
            for (const auto& symbol : alphabet) {
                convert_stream << std::dec << "\\x{" << std::hex << symbol << std::dec << "}";
            }
            regex += convert_stream.str();
            regex += "]*";
        } else if (m_util_s.re.is_intersection(expr)) { // Handle intersection.
            assert(false && "re.is_intersection(expr)");
        } else if (m_util_s.re.is_loop(expr)) { // Handle loop.
            assert(false && "re.is_loop(expr)");
        } else if (m_util_s.re.is_of_pred(expr)) { // Handle of predicate.
            assert(false && "re.is_of_pred(expr)");
        } else if (m_util_s.re.is_opt(expr)) { // Handle optional.
            SASSERT(expr->get_num_args() == 1);
            const auto child{ expr->get_arg(0) };
            SASSERT(is_app(child));
            regex = "(" + conv_to_regex_hex(to_app(child), m_util_s, m, alphabet) + ")?";
        } else if (m_util_s.re.is_range(expr)) { // Handle range.
            SASSERT(expr->get_num_args() == 2);
            const auto range_begin{ expr->get_arg(0) };
            const auto range_end{ expr->get_arg(1) };
            SASSERT(is_app(range_begin));
            SASSERT(is_app(range_end));
            const auto range_begin_value{ to_app(range_begin)->get_parameter(0).get_zstring()[0] };
            const auto range_end_value{ to_app(range_end)->get_parameter(0).get_zstring()[0] };
            auto current_value{ range_begin_value };
            std::stringstream convert_stream;
            while (current_value <= range_end_value) {
                convert_stream << std::dec << "\\x{" << std::hex << current_value << std::dec << "}";
                ++current_value;
            }
            regex = "[" + convert_stream.str() + "]";
        } else if (m_util_s.re.is_reverse(expr)) { // Handle reverse.
            assert(false && "re.is_reverse(expr)");
        } else if (m_util_s.re.is_union(expr)) { // Handle union (= or; A|B).
            SASSERT(expr->get_num_args() == 2);
            const auto left{ expr->get_arg(0) };
            const auto right{ expr->get_arg(1) };
            SASSERT(is_app(left));
            SASSERT(is_app(right));
            regex = "(" + conv_to_regex_hex(to_app(left), m_util_s, m, alphabet) + ")|(" + conv_to_regex_hex(to_app(right), m_util_s, m, alphabet) + ")";
        } else if (m_util_s.re.is_star(expr)) { // Handle star iteration.
            SASSERT(expr->get_num_args() == 1);
            const auto child{ expr->get_arg(0) };
            SASSERT(is_app(child));
            regex = "(" + conv_to_regex_hex(to_app(child), m_util_s, m, alphabet) + ")*";
        } else if (m_util_s.re.is_plus(expr)) { // Handle positive iteration.
            SASSERT(expr->get_num_args() == 1);
            const auto child{ expr->get_arg(0) };
            SASSERT(is_app(child));
            regex = "(" + conv_to_regex_hex(to_app(child), m_util_s, m, alphabet) + ")+";
        } else if(m_util_s.str.is_string(expr)) { // Handle string literal.
            SASSERT(expr->get_num_parameters() == 1);
            const zstring string_literal{ expr->get_parameter(0).get_zstring() };
            std::stringstream convert_stream;
            for (size_t i{ 0 }; i < string_literal.length(); ++i) {
                convert_stream << std::dec << "\\x{" << std::hex << string_literal[i] << std::dec << "}";
                // std::setfill('0') << std::setw(2) <<
            }
            regex = convert_stream.str();
        } else if(is_variable(expr, m_util_s)) { // Handle variable.
            assert(false && "is_variable(expr)");
        }

        //std::cout << regex << "\n";
        return regex;
    }

    [[nodiscard]] Nfa conv_to_nfa(const app *expression, const seq_util& m_util_s, const ast_manager& m,
                                  const std::set<uint32_t>& alphabet, bool make_complement) {
        Nfa nfa{};

        if (m_util_s.re.is_to_re(expression)) { // Handle conversion of to regex function call.
            SASSERT(expression->get_num_args() == 1);
            const auto arg{ expression->get_arg(0) };
            // Assume that expression inside re.to_re() function is a string of characters.
            if (!m_util_s.str.is_string(arg)) { // if to_re has something other than string literal
                throw_error("we support only string literals in str.to_re");
            }
            nfa = conv_to_nfa(to_app(arg), m_util_s, m, alphabet);
        } else if (m_util_s.re.is_concat(expression)) { // Handle regex concatenation.
            SASSERT(expression->get_num_args() > 0);
            nfa = conv_to_nfa(to_app(expression->get_arg(0)), m_util_s, m, alphabet);
            for (unsigned int i = 1; i < expression->get_num_args(); ++i) {
                nfa = Mata::Nfa::concatenate(nfa, conv_to_nfa(to_app(expression->get_arg(i)), m_util_s, m, alphabet));
            }
        } else if (m_util_s.re.is_antimirov_union(expression)) { // Handle Antimirov union.
            throw_error("antimirov union is unsupported");
        } else if (m_util_s.re.is_complement(expression)) { // Handle complement.
            SASSERT(expression->get_num_args() == 1);
            const auto child{ expression->get_arg(0) };
            SASSERT(is_app(child));
            nfa = conv_to_nfa(to_app(child), m_util_s, m, alphabet);
            // According to make_complement, we do complement at the end, so we just invert it
            make_complement = !make_complement;
        } else if (m_util_s.re.is_derivative(expression)) { // Handle derivative.
            throw_error("derivative is unsupported");
        } else if (m_util_s.re.is_diff(expression)) { // Handle diff.
            throw_error("regex difference is unsupported");
        } else if (m_util_s.re.is_dot_plus(expression)) { // Handle dot plus.
            nfa.initial.add(0);
            nfa.final.add(1);
            for (const auto& symbol : alphabet) {
                nfa.delta.add(0, symbol, 1);
                nfa.delta.add(1, symbol, 1);
            }
        } else if (m_util_s.re.is_empty(expression)) { // Handle empty language.
            // Do nothing, as nfa is initialized empty
        } else if (m_util_s.re.is_epsilon(expression)) { // Handle epsilon.
            nfa = Mata::Nfa::create_empty_string_nfa();
        } else if (m_util_s.re.is_full_char(expression)) { // Handle full char (single occurrence of any string symbol, '.').
            nfa.initial.add(0);
            nfa.final.add(1);
            for (const auto& symbol : alphabet) {
                nfa.delta.add(0, symbol, 1);
            }
        } else if (m_util_s.re.is_full_seq(expression)) {
            nfa.initial.add(0);
            nfa.final.add(0);
            for (const auto& symbol : alphabet) {
                nfa.delta.add(0, symbol, 0);
            }
        } else if (m_util_s.re.is_intersection(expression)) { // Handle intersection.
            SASSERT(expression->get_num_args() > 0);
            nfa = conv_to_nfa(to_app(expression->get_arg(0)), m_util_s, m, alphabet);
            for (unsigned int i = 1; i < expression->get_num_args(); ++i) {
                nfa = Mata::Nfa::intersection(nfa, conv_to_nfa(to_app(expression->get_arg(i)), m_util_s, m, alphabet));
            }
        } else if (m_util_s.re.is_loop(expression)) { // Handle loop.
            unsigned low, high;
            expr *body;
            bool is_high_set = false;
            if (m_util_s.re.is_loop(expression, body, low, high)) {
                is_high_set = true;
            } else if (m_util_s.re.is_loop(expression, body, low)) {
                is_high_set = false;
            } else {
                throw_error("loop should contain at least lower bound");
            }

            Nfa body_nfa = conv_to_nfa(to_app(body), m_util_s, m, alphabet);
            nfa = Mata::Nfa::create_empty_string_nfa();
            // we need to repeat body_nfa at least low times
            for (unsigned i = 0; i < low; ++i) {
                nfa = Mata::Nfa::concatenate(nfa, body_nfa);
            }

            // we will now either repeat body_nfa high-low times (if is_high_set) or
            // unlimited times (if it is not set), but we have to accept after each loop,
            // so we add an empty word into body_nfa by making some initial state final
            if (body_nfa.initial.empty()) {
                State new_state = body_nfa.add_state();
                body_nfa.initial.add(new_state);
                body_nfa.final.add(new_state);
            } else {
                body_nfa.final.add(*(body_nfa.initial.begin()));
            }

            if (is_high_set) {
                // if high is set, we repeat body_nfa another high-low times
                for (unsigned i = 0; i < high - low; ++i) {
                    nfa = Mata::Nfa::concatenate(nfa, body_nfa);
                }
            } else {
                // if high is not set, we can repeat body_nfa unlimited more times
                // so we do star operation on body_nfa and add it to end of nfa
                for (const auto& final : body_nfa.final) {
                    for (const auto& initial : body_nfa.initial) {
                        body_nfa.delta.add(final, Mata::Nfa::EPSILON, initial);
                    }
                }
                body_nfa.remove_epsilon();
                nfa = Mata::Nfa::concatenate(nfa, body_nfa);
            }
        } else if (m_util_s.re.is_of_pred(expression)) { // Handle of predicate.
            throw_error("of predicate is unsupported");
        } else if (m_util_s.re.is_opt(expression)) { // Handle optional.
            SASSERT(expression->get_num_args() == 1);
            const auto child{ expression->get_arg(0) };
            SASSERT(is_app(child));
            nfa = conv_to_nfa(to_app(child), m_util_s, m, alphabet);
            nfa.unify_initial();
            for (const auto& initial : nfa.initial) {
                nfa.final.add(initial);
            }
        } else if (m_util_s.re.is_range(expression)) { // Handle range.
            SASSERT(expression->get_num_args() == 2);
            const auto range_begin{ expression->get_arg(0) };
            const auto range_end{ expression->get_arg(1) };
            SASSERT(is_app(range_begin));
            SASSERT(is_app(range_end));
            const auto range_begin_value{ to_app(range_begin)->get_parameter(0).get_zstring()[0] };
            const auto range_end_value{ to_app(range_end)->get_parameter(0).get_zstring()[0] };

            nfa.initial.add(0);
            nfa.final.add(1);
            auto current_value{ range_begin_value };
            while (current_value <= range_end_value) {
                nfa.delta.add(0, current_value, 1);
                ++current_value;
            }
        } else if (m_util_s.re.is_reverse(expression)) { // Handle reverse.
            throw_error("reverse is unsupported");
        } else if (m_util_s.re.is_union(expression)) { // Handle union (= or; A|B).
            SASSERT(expression->get_num_args() == 2);
            const auto left{ expression->get_arg(0) };
            const auto right{ expression->get_arg(1) };
            SASSERT(is_app(left));
            SASSERT(is_app(right));
            nfa = Mata::Nfa::uni(conv_to_nfa(to_app(left), m_util_s, m, alphabet),
                                 conv_to_nfa(to_app(right), m_util_s, m, alphabet));
        } else if (m_util_s.re.is_star(expression)) { // Handle star iteration.
            SASSERT(expression->get_num_args() == 1);
            const auto child{ expression->get_arg(0) };
            SASSERT(is_app(child));
            nfa = conv_to_nfa(to_app(child), m_util_s, m, alphabet);
            for (const auto& final : nfa.final) {
                for (const auto& initial : nfa.initial) {
                    nfa.delta.add(final, Mata::Nfa::EPSILON, initial);
                }
            }
            nfa.remove_epsilon();

            // Make one initial final in order to accept empty string as is required by kleene-star.
            if (nfa.initial.empty()) {
                State new_state = nfa.add_state();
                nfa.initial.add(new_state);
                nfa.final.add(new_state);
            } else {
                nfa.final.add(*(nfa.initial.begin()));
            }
        } else if (m_util_s.re.is_plus(expression)) { // Handle positive iteration.
            SASSERT(expression->get_num_args() == 1);
            const auto child{ expression->get_arg(0) };
            SASSERT(is_app(child));
            nfa = conv_to_nfa(to_app(child), m_util_s, m, alphabet);
            for (const auto& final : nfa.final) {
                for (const auto& initial : nfa.initial) {
                    nfa.delta.add(final, Mata::Nfa::EPSILON, initial);
                }
            }
            nfa.remove_epsilon();
        } else if(m_util_s.str.is_string(expression)) { // Handle string literal.
            SASSERT(expression->get_num_parameters() == 1);
            nfa = AutAssignment::create_word_nfa(expression->get_parameter(0).get_zstring());
        } else if(is_variable(expression, m_util_s)) { // Handle variable.
            throw_error("variable in regexes are unsupported");
        } else {
            throw_error("unsupported operation in regex");
        }

        // Whether to create complement of the final automaton.
        // Warning: is_complement assumes we do the following, so if you to change this, go check is_complement first
        if (make_complement) {
            Mata::OnTheFlyAlphabet mata_alphabet{};
            for (const auto& symbol : alphabet) {
                mata_alphabet.add_new_symbol(std::to_string(symbol), symbol);
            }
            nfa = Mata::Nfa::complement(nfa, mata_alphabet);
        }
        return nfa;
    }

    void collect_terms(app* const ex, ast_manager& m, const seq_util& m_util_s, obj_map<expr, expr*>& pred_replace,
                       std::map<BasicTerm, expr_ref>& var_name, std::vector<BasicTerm>& terms) {

        if(m_util_s.str.is_string(ex)) { // Handle string literals.
            terms.emplace_back(BasicTermType::Literal, ex->get_parameter(0).get_zstring());
            return;
        }

        if(is_variable(ex, m_util_s)) {
            std::string var = ex->get_decl()->get_name().str();
            BasicTerm bvar(BasicTermType::Variable, var);
            terms.emplace_back(bvar);
            var_name.insert({bvar, expr_ref(ex, m)});
            return;
        }

        if(!m_util_s.str.is_concat(ex)) {
            expr* rpl = pred_replace.find(ex); // dies if it is not found
            collect_terms(to_app(rpl), m, m_util_s, pred_replace, var_name, terms);
            return;
        }

        SASSERT(ex->get_num_args() == 2);
        app *a_x = to_app(ex->get_arg(0));
        app *a_y = to_app(ex->get_arg(1));
        collect_terms(a_x, m, m_util_s, pred_replace, var_name, terms);
        collect_terms(a_y, m, m_util_s, pred_replace, var_name, terms);
    }

    BasicTerm get_variable_basic_term(expr *const variable) {
        SASSERT(is_app(variable));
        const app* variable_app{ to_app(variable) };
        SASSERT(variable_app->get_num_args() == 0);
        return BasicTerm{ BasicTermType::Variable, variable_app->get_decl()->get_name().str() };
    }

    void get_len_exprs(app* const ex, const seq_util& m_util_s, const ast_manager& m, obj_hashtable<app>& res) {
        if(m_util_s.str.is_length(ex)) {
            res.insert(ex);
            return;
        }

        for(unsigned i = 0; i < ex->get_num_args(); i++) {
            SASSERT(is_app(ex->get_arg(i)));
            app *arg = to_app(ex->get_arg(i));
            get_len_exprs(arg, m_util_s, m, res);
        }
    }

    bool is_len_sub(expr* val, expr* s, ast_manager& m, seq_util& m_util_s, arith_util& m_util_a, expr*& num_res) {
        expr* num = nullptr;
        expr* len = nullptr;
        expr* str = nullptr;
        if(!m_util_a.is_add(val, num, len)) {
            return false;
        }

        if(!m_util_a.is_int(num)) {
            return false;
        }
        num_res = num;

        if(!m_util_s.str.is_length(len, str) || str->hash() != s->hash()) {
            return false;
        } 
        
        return true;
    }
}
