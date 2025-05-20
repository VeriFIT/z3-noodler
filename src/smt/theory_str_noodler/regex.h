#ifndef _NOODLER_REGEX_H_
#define _NOODLER_REGEX_H_

#include <functional>
#include <list>
#include <set>
#include <stack>
#include <map>
#include <memory>
#include <queue>
#include <unordered_map>
#include <unordered_set>
#include <vector>

#include "smt/params/smt_params.h"
#include "ast/arith_decl_plugin.h"
#include "ast/seq_decl_plugin.h"
#include "smt/params/theory_str_params.h"
#include "util/scoped_vector.h"
#include "util/union_find.h"
#include "ast/rewriter/seq_rewriter.h"
#include "ast/rewriter/th_rewriter.h"

#include "formula.h"
#include "util.h"
#include "aut_assignment.h"

// FIXME most if not all these functions should probably be in theory_str_noodler

namespace smt::noodler::regex {
    using expr_pair = std::pair<expr_ref, expr_ref>;
    using expr_pair_flag = std::tuple<expr_ref, expr_ref, bool>;

    // bound for loop (above this number an optimized construction is used)
    const unsigned LOOP_BOUND = 5000;
    // simulation reduction bound in states (bigger automata are not reduced)
    const unsigned RED_BOUND = 1000;

    /**
     * @brief Info gathered about a regex. 
     * - min_length: length of shortest words in the regex. In fact it expresses that in the regex there is no 
     *      word shorter than min_length. It does not mean that regex contains a word of length exactly min_length. 
     *      If empty == l_true or l_undef, this value is not valid. 
     * - universal: is regex universal?
     * - empty: is regex empty?
     */
    struct RegexInfo {
        unsigned min_length;
        lbool universal;
        lbool empty;
    };

    /**
     * @brief Alphabet wrapper for Z3 alphabet represented by std::set<mata::Symbol> and a Mata alphabet.
     */
    struct Alphabet {
        std::set<mata::Symbol> alphabet;
        mata::OnTheFlyAlphabet mata_alphabet;
        
        Alphabet(const std::set<mata::Symbol>& alph) : alphabet(alph) {
            for (const auto& symbol : alph) {
                this->mata_alphabet.add_new_symbol(std::to_string(symbol), symbol);
            }
        }

        /// @brief Returns any symbol that is not in the alphabet
        mata::Symbol get_unused_symbol() const {
            // std::set is ordered, so alphabet is also ordered
            if (*alphabet.begin() != 0) {
                return 0;
            } else {
                auto it = alphabet.begin();
                mata::Symbol s = *it;
                ++it;
                while (it != alphabet.end()) {
                    if (s+1 != *it) {
                        return s+1;
                    }
                    ++it;
                }
                return (*it)+1;
            }
        }

        /// @brief Return zstring corresponding the the word @p word, where dummy symbol is replaced with some valid symbol not in the alphabet.
        zstring get_string_from_mata_word(mata::Word word) const {
            zstring res;
            mata::Symbol unused_symbol = get_unused_symbol();
            std::replace(word.begin(), word.end(), util::get_dummy_symbol(), unused_symbol);
            return zstring(word.size(), word.data());
        }
    };

    /**
     * Extract symbols from a given expression @p ex. Append to the output parameter @p alphabet.
     * @param[in] ex Expression to be checked for symbols.
     * @param[in] m_util_s Seq util for AST.
     * @param[out] alphabet A set of symbols with where found symbols are appended to.
     */
    void extract_symbols(expr* const ex, const seq_util& m_util_s, std::set<uint32_t>& alphabet);

    /**
     * Convert expression @p expr to NFA.
     * @param[in] expression Expression to be converted to NFA.
     * @param[in] m_util_s Seq util for AST.
     * @param[in] alphabet Alphabet to be used in re.allchar (SMT2: '.') expressions.
     * @param[in] determinize Determinize intermediate automata
     * @param[in] make_complement Whether to make complement of the passed @p expr instead.
     * @return The resulting regex.
     */
    [[nodiscard]] mata::nfa::Nfa conv_to_nfa(app *expression, const seq_util& m_util_s, const ast_manager& m,
                                             const Alphabet& alphabet, bool determinize = false, bool make_complement = false);

    /**
     * @brief Get basic information about the regular expression in the form of RegexInfo (see the description above). 
     * RegexInfo gathers information about emptiness; universality; length of shortest words
     * 
     * @param expression Regex to be checked
     * @param m_util_s string ast util
     * @param m ast manager
     * @return RegexInfo 
     */
    RegexInfo get_regex_info(const app *expression, const seq_util& m_util_s);

    /**
     * @brief Create bounded iteration of a given automaton. 
     * 
     * @param body_nfa Core NFA
     * @param count Number of concatenations
     * @return mata::nfa::Nfa NFA
     */
    mata::nfa::Nfa create_large_concat(const mata::nfa::Nfa& body_nfa, unsigned count);

    /**
     * @brief Get the sum of loops of a regex (loop inside a loop is multiplied)
     * 
     * @param reg some regular expression predicate (can be also string literal/var)
     * @param m_util_s string ast util
     * @return sum of loops inside @p regex, with nested loops multiplied 
     */
    unsigned get_loop_sum(const app* reg, const seq_util& m_util_s);

    class regex_model_fail : public default_exception {
    public:
        regex_model_fail() : default_exception("Failed to find model of a regex") {}
    };

    /**
     * @brief Try to g et some word accepted by @p regex
     * 
     * It currently cannot handle intersection, complement, or string variables inside regex.
     * 
     * @param regex Regex to be checked
     * @param m_util_s string ast util
     * @return word accepted by @p regex
     * @throws regex_model_fail if the model cannot be found (either regex represents empty language, or it contains intersection/complement/string variables, which this function currently cannot handle)
     */
    zstring get_model_from_regex(const app *regex, const seq_util& m_util_s);

    /// Prefix tree for multiple replace_all applications so that we can construct transducer simultaneously (see https://github.com/VeriFIT/z3-noodler/pull/227#issuecomment-2893972253 for small explanation)
    class ReplaceAllPrefixTree {
        std::set<unsigned> replace_chars; /// the chars occuring in the replace strings of replace_all operations (except the ones of length 1)
        std::set<unsigned> find_delimiters; /// the chars occuring in the first position of find strings of replace_all operation (and the replace strings of length 1)
        std::set<unsigned> find_non_delimiters; /// the chars occuring in the second, third, etc. find strings of replace_all operations
        mata::nfa::Nfa prefix_automaton{1,{0}}; /// the prefix "tree" for find strings of replace_all operations
        std::map<mata::nfa::State, mata::Word> replacing_map{{0, {}}}; /// maps states of prefix_automaton that to the string that should be replaced by (for find strings it will be corresponding replace, otherwise the prefix)
        std::map<mata::Symbol, std::set<mata::nfa::State>> one_symbol_replace_to_prefix_state; /// for each symbol w (|w| = 1) and q where w = replacing_map[q], we have q \in one_symbol_replace_to_prefix_state[w]

        /**
         * @brief Get the next state of prefix tree (if exists) from state @p from trough symbol @p symbol
         * 
         * @param from the state from which we go
         * @param symbol the symbol through which we go
         * @return the next state (nullopt if it does not exists)
         */
        std::optional<mata::nfa::State> get_next_state(mata::nfa::State from, mata::Symbol symbol) {
            auto next_state_it = prefix_automaton.delta[from].find(symbol);
            if (next_state_it != prefix_automaton.delta[from].end()) {
                SASSERT(next_state_it->targets.size() == 1);
                return next_state_it->targets.front();
            } else {
                return std::nullopt;
            }
        }

        /// true iff @p state is the last state on the path of prefix tree, i.e., no successors (represents that the path to this state should be replaced in input string by replacing_map[state])
        bool is_prefix_state_last(mata::nfa::State state) {
            return prefix_automaton.delta[state].empty();
        }

        /// true iff @p state is final in the prefix tree (represents the situation that there was some match of find string from the previous final state)
        bool is_prefix_state_final(mata::nfa::State state) {
            return prefix_automaton.final[state];
        }

    public:
        ReplaceAllPrefixTree() = default;
        /**
         * @brief Add another replace_all application where each @p find should be replaced by @p replace
         * 
         * It also checks if this application can be added to existing ones by some simple heuristics:
         *      - @p find must be of the form where the first symbol (delimiter) is different than all
         *        the other symbols (non-delimiters) of @p find and furthermore, each previous and current
         *        @p find must have these delimiters different than all the non-delimiters of previous and
         *        the current @p find. The point of this rule is so that we cannot match a word while we
         *        are already matching some. For example if we have
         *          (str.replace_all (str.replace_all x "bad" "c") "a" "f")
         *        then for the word x="bac", it should transform it into "bfc". However, we would start
         *        matching on the first character 'b' expecting the word "bad". But on 'c', we would realise
         *        it is not correct and we would have to go back and check if there was not some 'a'.
         *        Currently, this is not gonna happen, so it is not allowed.
         *      - @p find cannot be a prefix of the find string of some previous replace_all
         *        operation. For example if we had "ab" is replaced with "c" and then we
         *        would want replace_all where "a" is replaced with "d", the simultaneous
         *        replacing would always replace "a" first, which is incorrect, "ab" should
         *        be replaced.
         *      - @p find cannot contain any symbol that occurs in any of the previous replace strings.
         *        This could cause problems, for example, if we have
         *          (str.replace_all (str.replace_all x "dc" "g") "ag" "r")
         *        then this would change x="adc" to "r". However, the simultaneus matching would only match "dc",
         *        transforming it into "ar" and we would not go back to check that this can be again transformed.
         *      - The previous condition is slightly weaker, we look at the replace strings of length 1 as delimiters,
         *        therefore we allow for example
         *          (str.replace_all (str.replace_all x "abc" "d") "de" "f")
         *        Here we can remember that if we match "abc" in input string (replaced by "d"), we can continue,
         *        possibly also matching "de".
         * If it cannot be added, the function returns false and you should get the transducer.
         * 
         * @param find the string whose every occurence we want to replace
         * @param replace what to replace with
         * @return true If the replace_all application is added to this prefix tree
         */
        bool add_find(const zstring& find, const zstring& replace);

        /**
         * @brief Creates a transducer replacing all added finds by their replaces simultaneously
         * 
         * @param mata_alph The alphabet used for creating the transducer
         * @return The simultaneous transducer
         */
        mata::nft::Nft create_transducer(mata::Alphabet* mata_alph);
    };

    /**
     * @brief Gather transducer constraint (replace_all, replace_re_all) from a concatenation. Recursively applies also on 
     * nested calls of replace_all, replace_re_all.
     * 
     * @param ex Expression to gather replaces from.
     * @param m AST manager
     * @param m_util_s Seq util for AST.
     * @param pred_replace Replacement of predicate and functions
     * @param var_name Mapping of BasicTerm variables to z3 variables
     * @param mata_alph Mata alphabet containing symbols from the current instance
     * @param[out] transducer_preds Newly created transducer constraints
     */
    void gather_transducer_constraints(app* ex, ast_manager& m, const seq_util& m_util_s, obj_map<expr, expr*>& pred_replace, 
        std::map<BasicTerm, expr_ref>& var_name, mata::Alphabet* mata_alph, Formula& transducer_preds);

}

#endif
