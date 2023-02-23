#include <cassert>
#include <mata/re2parser.hh>

#include "util.h"
#include "theory_str_noodler.h"
#include "inclusion_graph.h"
#include "aut_assignment.h"

namespace {
    using Mata::Nfa::Nfa;
}

namespace smt::noodler::util {
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
            // Assume that expression inside re.to_re() function is a string of characters.
            SASSERT(ex_app->get_num_args() == 1);
            const auto arg{ ex_app->get_arg(0) };
            extract_symbols(to_app(arg), m_util_s, m, alphabet);
            return;
        } else if (m_util_s.re.is_concat(ex_app)) { // Handle concatenation.
            SASSERT(ex_app->get_num_args() == 2);
            const auto left{ex_app->get_arg(0)};
            const auto right{ex_app->get_arg(1)};
            SASSERT(is_app(left));
            SASSERT(is_app(right));
            extract_symbols(to_app(left), m_util_s, m, alphabet);
            extract_symbols(to_app(right), m_util_s, m, alphabet);
            return;
        } else if (m_util_s.re.is_antimirov_union(ex_app)) { // Handle Antimirov union.
            assert(false && "re.is_antimirov_union(ex_app)");
        } else if (m_util_s.re.is_complement(ex_app)) { // Handle complement.
            assert(false && "re.is_complement(ex_app)");
        } else if (m_util_s.re.is_derivative(ex_app)) { // Handle derivative.
            assert(false && "re.is_derivative(ex_app)");
        } else if (m_util_s.re.is_diff(ex_app)) { // Handle diff.
            assert(false && "re.is_diff(ex_app)");
        } else if (m_util_s.re.is_dot_plus(ex_app)) { // Handle dot plus.
            assert(false && "re.is_dot_plus(ex_app)");
        } else if (m_util_s.re.is_empty(ex_app)) { // Handle empty string.
            assert(false && "re.is_empty(ex_app)");
        } else if (m_util_s.re.is_epsilon(ex_app)) { // Handle epsilon.
            assert(false && "re.is_epsilon(ex_app)");
        } else if (m_util_s.re.is_full_char(ex_app)) {
            // Handle full char (single occurrence of any string symbol, '.') (SMT2: re.allchar).
            return;
        } else if (m_util_s.re.is_full_seq(ex_app)) {
            // Handle full sequence of characters (any sequence of characters, '.*') (SMT2: re.all).
            return;
        } else if (m_util_s.re.is_intersection(ex_app)) { // Handle intersection.
            assert(false && "re.is_intersection(ex_app)");
        } else if (m_util_s.re.is_loop(ex_app)) { // Handle loop.
            assert(false && "re.is_loop(ex_app)");
        } else if (m_util_s.re.is_of_pred(ex_app)) { // Handle of predicate.
            assert(false && "re.is_of_pred(ex_app)");
        } else if (m_util_s.re.is_opt(ex_app)) { // Handle optional.
            SASSERT(ex_app->get_num_args() == 1);
            const auto child{ ex_app->get_arg(0) };
            SASSERT(is_app(child));
            extract_symbols(to_app(child), m_util_s, m, alphabet);
            return;
        } else if (m_util_s.re.is_range(ex_app)) { // Handle range.
            assert(false && "re.is_range(ex_app)");
        } else if (m_util_s.re.is_reverse(ex_app)) { // Handle reverse.
            assert(false && "re.is_reverse(ex_app)");
        } else if (m_util_s.re.is_union(ex_app)) { // Handle union (= or; A|B).
            SASSERT(ex_app->get_num_args() == 2);
            const auto left{ ex_app->get_arg(0) };
            const auto right{ ex_app->get_arg(1) };
            SASSERT(is_app(left));
            SASSERT(is_app(right));
            extract_symbols(to_app(left), m_util_s, m, alphabet);
            extract_symbols(to_app(right), m_util_s, m, alphabet);
            return;
        } else if (m_util_s.re.is_star(ex_app)) { // Handle star iteration.
            SASSERT(ex_app->get_num_args() == 1);
            const auto child{ ex_app->get_arg(0) };
            SASSERT(is_app(child));
            extract_symbols(to_app(child), m_util_s, m, alphabet);
            return;
        } else if (m_util_s.re.is_plus(ex_app)) { // Handle positive iteration.
            SASSERT(ex_app->get_num_args() == 1);
            const auto child{ ex_app->get_arg(0) };
            SASSERT(is_app(child));
            extract_symbols(to_app(child), m_util_s, m, alphabet);
            return;
        } else if(is_variable(ex_app, m_util_s)) { // Handle variable.
            assert(false && "is_variable(ex_app)");
        }

        // When ex is not string literal, variable, nor regex, recursively traverse the AST to find symbols.
        for(unsigned i = 0; i < ex_app->get_num_args(); i++) {
            SASSERT(is_app(ex_app->get_arg(i)));
            app *arg = to_app(ex_app->get_arg(i));
            extract_symbols(arg, m_util_s, m, alphabet);
        }
    }

    void get_str_variables(expr* const ex, const seq_util& m_util_s, const ast_manager& m, obj_hashtable<expr>& res) {
        if(m_util_s.str.is_string(ex)) {
            return;
        }

        if(is_str_variable(ex, m_util_s)) {
            res.insert(ex);
            return;
        }

        SASSERT(is_app(ex));
        app* ex_app{ to_app(ex) };

        for(unsigned i = 0; i < ex_app->get_num_args(); i++) {
            SASSERT(is_app(ex_app->get_arg(i)));
            app *arg = to_app(ex_app->get_arg(i));
            get_str_variables(arg, m_util_s, m, res);
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

        if (m_util_s.is_string(expression->get_sort()) &&
            is_app(expression) && to_app(expression)->get_num_args() == 0) {
            return true;
        }

        return false;
    }

    std::set<uint32_t> get_dummy_symbols(const vector<expr_pair>& disequations, std::set<uint32_t>& symbols_to_append_to) {
        std::set<uint32_t> dummy_symbols{};
        uint32_t dummy_symbol{ 0 };
        const size_t disequations_number{ disequations.size() };
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
        return symbols_in_formula;
    }

    AutAssignment create_aut_assignment_for_formula(
            const vector<expr_pair>& equations,
            const vector<expr_pair>& disequations,
            const vector<expr_pair_flag>& regexes,
            const seq_util& m_util_s,
            const ast_manager& m,
            const std::set<uint32_t>& noodler_alphabet
    ) {
        // Find all variables in the whole formula.
        std::unordered_set<std::string> variables_in_formula{};
        for (const auto &word_equation: equations) {
            util::get_variable_names(word_equation.first, m_util_s, m, variables_in_formula);
            util::get_variable_names(word_equation.second, m_util_s, m, variables_in_formula);
        }
        for (const auto &word_equation: disequations) {
            util::get_variable_names(word_equation.first, m_util_s, m, variables_in_formula);
            util::get_variable_names(word_equation.second, m_util_s, m, variables_in_formula);
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
            BasicTerm variable_term{ BasicTermType::Variable, variable_name };
            assert(aut_assignment.find(variable_term) == aut_assignment.end());

            const bool make_complement{ !std::get<2>(word_equation) };
            Nfa nfa{ conv_to_nfa_hex(to_app(std::get<1>(word_equation)), m_util_s, m, noodler_alphabet, make_complement) };
            aut_assignment[variable_term] = std::make_shared<Nfa>(std::forward<Nfa>(std::move(nfa)));
        }

        // Assign sigma start automata for all yet unassigned variables.
        Mata::OnTheFlyAlphabet mata_alphabet{};
        std::stringstream string_stream;
        string_stream << std::hex;
        std::string hex_symbol_string;
        for (const uint32_t symbol : noodler_alphabet) {
            string_stream << symbol;
            string_stream >> hex_symbol_string;
            hex_symbol_string = "\\x{" + hex_symbol_string + "}";
            mata_alphabet.add_new_symbol(hex_symbol_string, symbol);
            string_stream.clear();
        }

        const Nfa nfa_sigma_star{ Mata::Nfa::create_sigma_star_nfa(&mata_alphabet) };
        for (const auto& variable_name : variables_in_formula) {
            if (variables_with_regex.find(variable_name) == variables_with_regex.end()) {
                BasicTerm variable_term{ BasicTermType::Variable, variable_name };
                assert(aut_assignment.find(variable_term) == aut_assignment.end());
                aut_assignment[variable_term] = std::make_shared<Nfa>(nfa_sigma_star);
            }
        }

        // DEBUG.
        //for (const auto& single_aut_assignment: aut_assignment) {
        //    std::cout << single_aut_assignment.first.get_name() << ":\n";
        //    single_aut_assignment.second->print_to_DOT(std::cout);
        //}

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
            assert(false && "re.is_range(expr)");
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
            const zstring string_literal{ zstring{ expr->get_parameter(0).get_zstring().encode() } };
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

    [[nodiscard]] Nfa conv_to_nfa_hex(const app *expr, const seq_util& m_util_s, const ast_manager& m,
                                              const std::set<uint32_t>& alphabet, bool make_complement) {
        Nfa nfa{};

        if (m_util_s.re.is_to_re(expr)) { // Handle conversion of to regex function call.
            // Assume that expression inside re.to_re() function is a string of characters.
            SASSERT(expr->get_num_args() == 1);
            const auto arg{ expr->get_arg(0) };
            nfa = conv_to_nfa_hex(to_app(arg), m_util_s, m, alphabet);
        } else if (m_util_s.re.is_concat(expr)) { // Handle concatenation.
            SASSERT(expr->get_num_args() == 2);
            const auto left{ expr->get_arg(0) };
            const auto right{ expr->get_arg(1) };
            SASSERT(is_app(left));
            SASSERT(is_app(right));
            auto first_nfa{ conv_to_nfa_hex(to_app(left), m_util_s, m, alphabet) };
            auto second_nfa{ conv_to_nfa_hex(to_app(right), m_util_s, m, alphabet) };
            nfa = Mata::Nfa::concatenate(first_nfa, second_nfa);
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
            nfa.initial.add(0);
            nfa.final.add(1);
            for (const auto& symbol : alphabet) {
                nfa.delta.add(0, symbol, 1);
            }
        } else if (m_util_s.re.is_full_seq(expr)) {
            nfa.initial.add(0);
            nfa.final.add(0);
            for (const auto& symbol : alphabet) {
                nfa.delta.add(0, symbol, 0);
            }
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
            nfa = conv_to_nfa_hex(to_app(child), m_util_s, m, alphabet);
            for (const auto& initial : nfa.initial) {
                nfa.final.add(initial);
            }
        } else if (m_util_s.re.is_range(expr)) { // Handle range.
            assert(false && "re.is_range(expr)");
        } else if (m_util_s.re.is_reverse(expr)) { // Handle reverse.
            assert(false && "re.is_reverse(expr)");
        } else if (m_util_s.re.is_union(expr)) { // Handle union (= or; A|B).
            SASSERT(expr->get_num_args() == 2);
            const auto left{ expr->get_arg(0) };
            const auto right{ expr->get_arg(1) };
            SASSERT(is_app(left));
            SASSERT(is_app(right));
            nfa = Mata::Nfa::uni(conv_to_nfa_hex(to_app(left), m_util_s, m, alphabet),
                                 conv_to_nfa_hex(to_app(right), m_util_s, m, alphabet));
        } else if (m_util_s.re.is_star(expr)) { // Handle star iteration.
            SASSERT(expr->get_num_args() == 1);
            const auto child{ expr->get_arg(0) };
            SASSERT(is_app(child));
            nfa = conv_to_nfa_hex(to_app(child), m_util_s, m, alphabet);
            for (const auto& final : nfa.final) {
                for (const auto& initial : nfa.initial) {
                    nfa.delta.add(final, Mata::Nfa::EPSILON, initial);
                }
            }
            nfa.remove_epsilon();

            // Make one initial final in order to accept empty string as is required by kleene-star.
            SASSERT(!nfa.initial.empty());
            nfa.final.add(*nfa.initial.begin());
        } else if (m_util_s.re.is_plus(expr)) { // Handle positive iteration.
            SASSERT(expr->get_num_args() == 1);
            const auto child{ expr->get_arg(0) };
            SASSERT(is_app(child));
            nfa = conv_to_nfa_hex(to_app(child), m_util_s, m, alphabet);
            for (const auto& final : nfa.final) {
                for (const auto& initial : nfa.initial) {
                    nfa.delta.add(final, Mata::Nfa::EPSILON, initial);
                }
            }
            nfa.remove_epsilon();
        } else if(m_util_s.str.is_string(expr)) { // Handle string literal.
            SASSERT(expr->get_num_parameters() == 1);
            const zstring string_literal{ zstring{ expr->get_parameter(0).get_zstring().encode() } };
            std::stringstream convert_stream;
            nfa.initial.add(0);
            size_t state{ 0 };
            for (; state < string_literal.length(); ++state) {
                nfa.delta.add(state, string_literal[state], state + 1);
            }
            nfa.final.add(state);
        } else if(is_variable(expr, m_util_s)) { // Handle variable.
            assert(false && "is_variable(expr)");
        }

        // Whether to create complement of the final automaton.
        if (make_complement) {
            Mata::OnTheFlyAlphabet mata_alphabet{ Mata::Nfa::create_alphabet(nfa) };
            nfa = Mata::Nfa::complement(nfa, mata_alphabet);
        }
        return nfa;
    }

    void collect_terms(app* const ex, ast_manager& m, const seq_util& m_util_s, obj_map<expr, expr*>& pred_replace,
                       std::vector<BasicTerm>& terms) {

        if(m_util_s.str.is_string(ex)) {
            terms.emplace_back(BasicTermType::Literal, util::conv_to_regex_hex(ex, m_util_s, m, {}));
            return;
        }

        if(is_variable(ex, m_util_s)) {
            std::string var = ex->get_decl()->get_name().str();
            terms.emplace_back(BasicTermType::Variable, var);
            return;
        }

        if(!m_util_s.str.is_concat(ex)) {
            expr* rpl = pred_replace.find(ex); // dies if it is not found
            collect_terms(to_app(rpl), m, m_util_s, pred_replace, terms);
            return;
        }

        SASSERT(ex->get_num_args() == 2);
        app *a_x = to_app(ex->get_arg(0));
        app *a_y = to_app(ex->get_arg(1));
        collect_terms(a_x, m, m_util_s, pred_replace, terms);
        collect_terms(a_y, m, m_util_s, pred_replace, terms);
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
}
