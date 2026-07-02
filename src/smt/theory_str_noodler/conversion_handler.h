#ifndef _NOODLER_CONVERSION_HANDLER_H_
#define _NOODLER_CONVERSION_HANDLER_H_

#include <optional>

#include "solving_state.h"

namespace smt::noodler {

    /// Class for handling string-number conversions, especially to generate the formula to encode them for a given solution of DecisionProcedure
    class ConversionHandler {
    private:
        std::vector<TermConversion> conversions;

        /// solution for which we compute the formula encoding conversions
        SolvingState solution;
        /// The set of vars s_i, such that there exists "c = to_code(s)" or "s = from_code(c)" in conversions, where s is substituted by s_1 ... s_i ... s_n in the solution.
        std::set<BasicTerm> code_subst_vars;
        /// The set of vars s_i, such that there exists "i = to_int(s)" or "s = from_int(i)" in conversions, where s is substituted by s_1 ... s_i ... s_n in the solution.
        std::set<BasicTerm> int_subst_vars;
        /// The set of vars s_i, such that there exists "r = to_real(s)" or "s = from_real(r)" in conversions, where s is substituted by s_1 ... s_i ... s_n in the solution.
        std::set<BasicTerm> real_subst_vars;

        // STUFF FOR CODE CONVERSIONS

        /**
         * @brief Get the formula for to_code/from_code substituting variable @p code_subst_var
         * 
         * It basically succinctly encodes that code_version_of(code_subst_var) is equal to one of to_code(w) for some w \in solution.aut_ass.at(code_subst_var) while
         * keeping the correspondence between |code_subst_var| and |w|.
         */
        LenNode get_formula_for_code_subst_var(const BasicTerm& code_subst_var);

        /// Get the formula encoding to_code/from_code conversion
        LenNode get_formula_for_code_conversion(const TermConversion& conv);


        // STUFF FOR INT/REAL CONVERSIONS

        // Special automata used for computing int and real conversions :
        // only_digits is automaton representing all valid inputs for integers (they contain only digits)
        // - we also keep empty word, because we will use it for substituted vars, and one of them can be empty, while other has only digits (for example s1="45", s2="" but s=s1s2 = "45" is valid)
        const mata::nfa::Nfa only_digits;
        // automaton representing all real numbers (two numbers divided by ".")
        // - we also keep the word ".", because the substituted var could be surrounded by other vars that will represent the whole/decimal part
        const mata::nfa::Nfa real_numbers;
        // The following two automata also depend on the alphabet in solution
        // automaton representing all non-valid inputs for integers (contains some non-digit)
        mata::nfa::Nfa contain_non_digit;
        // automaton representing all non-valid (real/integer) numbers
        mata::nfa::Nfa non_number;

        /// Used to underapproximate infinite languages for valid int/real cases
        unsigned underapprox_length;

        /// If @p aut has finite language, gets the (overapproximated) length of the longest word in @p aut and if not, returns underapprox_length while setting @p precision to LenNodePrecision::UNDERAPPROX
        unsigned max_length_of_word_in_aut(const mata::nfa::Nfa aut, LenNodePrecision& precision) {
            if (aut.is_acyclic()) {
                // there is a finite number of words in aut => the longest possible word is aut.num_of_states()-1
                return aut.num_of_states()-1;
            } else {
                // there is infinite number of such words => we need to underapproximate
                STRACE(str_conversion, tout << "infinite NFA for which we need to do underapproximation:" << std::endl << aut << std::endl;);
                precision = LenNodePrecision::UNDERAPPROX;
                return underapprox_length;
            }
        };

        /// maps each var from int_subst_vars and real_subst_vars to each length of a valid representation of integer in solution.aut_ass[var]
        std::map<BasicTerm,std::vector<unsigned>> int_subst_vars_to_possible_valid_lengths;
        /// maps each var from real_subst_vars to each length of a valid representation of real number (with the position of dot) in solution.aut_ass[var]
        std::map<BasicTerm,std::vector<std::pair<unsigned,unsigned>>> real_subst_vars_to_possible_valid_lengths_and_dot_positions;

        /**
         * @brief Encodes the case that @p int_real_subst_var does not encode a valid number
         * 
         * @param int_real_subst_var int or real substituting var
         */
        LenNode get_formula_for_invalid_case(const BasicTerm& int_real_subst_var);

        /**
         * @brief Encodes the case that @p int_real_subst_var encodes a valid integer number
         * 
         * @param int_real_subst_var int or real substituting var
         */
        LenNode get_formula_for_valid_int_case(const BasicTerm& int_real_subst_var, LenNodePrecision& precision);

        /**
         * @brief Encodes the case that @p int_real_subst_var encodes a valid real number (but not integers)
         * 
         * @param int_real_subst_var int or real substituting var
         */
        LenNode get_formula_for_valid_real_case(const BasicTerm& int_real_subst_var, LenNodePrecision& precision);


        /**
         * @brief Get the formula encoding that arithmetic variable @p var is any of the numbers encoded by some interval word from @p interval_words
         */
        LenNode encode_interval_words(const BasicTerm& var, const std::vector<IntervalWord>& interval_words);

        /**
         * @brief Get the formula for int or real substituting variable @p int_real_subst_var
         * 
         * In the case for int substituting variable, it succinctly encodes that int_version_of(int_real_subst_var) is one of to_int(w) for some w \in solution.aut_ass.at(int_real_subst_var)
         * while keeping the correspondence between |int_real_subst_var|, |w|, and code_version_of(s).
         * In the case of real substituting variable, it also encodes that dot_position_of(int_real_subst_var) is the position of the decimal delimiter of some w \in solution.aut_ass.at(int_real_subst_var)
         * with corresponding whole_part_of(int_real_subst_var) and decimal_part_of(int_real_subst_var).
         * 
         * Note that for w = "", we do not put int_version_of(int_real_subst_var) == -1 but instead int_version_of(int_real_subst_var) == 0.
         * Furthermore, for w = ".", we put dot_position_of(int_real_subst_var) == 1 and whole_part_of(int_real_subst_var) == decimal_part_of(int_real_subst_var) == 0.
         * 
         * @param int_real_subst_var int or real substituting var
         * @return std::pair<LenNode, LenNodePrecision> The resulting formula with its precision (can be underapproximating)
         */
        std::pair<LenNode, LenNodePrecision> get_formula_for_int_real_subst_var(const BasicTerm& int_real_subst_var);

        /**
         * @brief For subst_vars=<s1,...,sn>, encodes into @p result all possible numbers represented by the string s=s1.s2...sn given their lengths in @p lengths_of_subst_vars and the possible decimal delimiter position given by @p index_of_subst_var_with_dot_and_dot_position
         * 
         * @param result the resulting number
         * @param subst_vars the vars whose concatenation should encode a number
         * @param lengths_of_subst_vars each index i contains possible length of s_i
         * @param index_of_subst_var_with_dot_and_dot_position if defined, the pair <i,d> where s_i should contain decimal delimiter on position d
         * @return LenNode 
         */
        LenNode get_formula_for_number_conversion(BasicTerm result, const std::vector<BasicTerm>& subst_vars, std::vector<unsigned> lengths_of_subst_vars, std::optional<std::pair<size_t,unsigned>> index_of_subst_var_with_dot_and_dot_position);


        /// Get the formula encoding to_int/from_int/to_real/from_real conversion in @p conv
        LenNode get_formula_for_int_real_conversion(const TermConversion& conv);

    public:
        ConversionHandler(std::vector<TermConversion> conversions, unsigned underapprox_length) : conversions(conversions), only_digits(AutAssignment::digit_automaton_with_epsilon()), real_numbers(AutAssignment::decimal_automaton()), underapprox_length(underapprox_length) {
        };

        /// Gets a solution for which we want to compute the LIA formula (can be called multiple times to get formula for different solutions)
        void initialize_solution(SolvingState solution);

        /**
         * @brief Gets a LI(R)A formula encoding the conversions based on a given solution from initialize_solution
         * 
         * @param subst_vars_not_needed_to_be_handled substituting vars for which we do not need to create encoding subformulas because they are handled differently (for example by parikh image)
         * @return std::pair<LenNode, LenNodePrecision> resulting formula with its precision (can be underapproximating)
         */
        std::pair<LenNode, LenNodePrecision> get_formula_encoding_conversions(const std::set<BasicTerm> subst_vars_not_needed_to_be_handled);

        /// The set of vars s_i, such that there exists "c = to_code(s)" or "s = from_code(c)" in conversions, where s is substituted by s_1 ... s_i ... s_n in the solution.
        const std::set<BasicTerm>& get_code_subst_vars() const { return code_subst_vars; }

        /// The set of vars s_i, such that there exists "i = to_int(s)" or "s = from_int(i)" in conversions, where s is substituted by s_1 ... s_i ... s_n in the solution.
        const std::set<BasicTerm>& get_int_subst_vars() const { return int_subst_vars; }

        /// The set of vars s_i, such that there exists "r = to_real(s)" or "s = from_real(r)" in conversions, where s is substituted by s_1 ... s_i ... s_n in the solution.
        const std::set<BasicTerm>& get_real_subst_vars() const { return real_subst_vars; }

        bool is_var_code_subst_var(const BasicTerm& var) const { return code_subst_vars.contains(var); }

        bool is_var_int_subst_var(const BasicTerm& var) const { return int_subst_vars.contains(var); }

        bool is_var_real_subst_var(const BasicTerm& var) const { return real_subst_vars.contains(var); }

        /// Get all the string variables occuring in conversions
        std::set<BasicTerm> get_string_vars_in_conversions() const {
            std::set<BasicTerm> conv_string_vars;
            for (const auto &conv : conversions) {
                conv_string_vars.insert(conv.string_var);
            }
            return conv_string_vars;
        }

        const std::vector<TermConversion>& get_conversions() const { return conversions; }

        /**
         * @brief Adds a conversion @p conversion to the list of conversions handled by this ConversionHandler
         * 
         * WARNING: It is assumed that after initialize_solution is called, this function will never be called
         */
        void add_conversion(TermConversion conversion) { conversions.push_back(conversion); }

        /// Are there any conversions this ConversionHandler is handling?
        bool are_there_any_conversions() const { return !conversions.empty(); }

        /// Returns the code var version of @p var used to encode code-string conversions
        BasicTerm code_version_of(const BasicTerm& var) { return util::mk_internal_noodler_var(var.get_name() + zstring("!to_code")); }

        /// Returns the int var version of @p var used to encode int-string conversions
        BasicTerm int_version_of(const BasicTerm& var) { return util::mk_internal_noodler_var(var.get_name() + zstring("!to_int")); }

        /// Returns the variable for @p var encoding the decimal separator position in @p var
        BasicTerm dot_position_of(const BasicTerm& var) { return util::mk_internal_noodler_var(var.get_name() + zstring("!dot_position")); }

        /// Returns the variable for @p var encoding the whole part before the decimal separator in @p var
        BasicTerm whole_part_of(const BasicTerm& var) { return util::mk_internal_noodler_var(var.get_name() + zstring("!whole_part")); }

        /// Returns the variable for @p var encoding the decimal part after the decimal separator in @p var
        BasicTerm decimal_part_of(const BasicTerm& var) { return util::mk_internal_noodler_var(var.get_name() + zstring("!decimal_part")); }

        /// Get all variables needed to generate model for conversions
        std::vector<BasicTerm> get_arith_vars_needed_for_model();

        /// TODO: add function to handle model generation for substituting vars

        /**
         * @brief Get sound (but possibly not tight) bounds on the value of str.to_int(x) derivable just from the
         * language of @p x, without running the full decision procedure.
         *
         * This is meant to be used as a cheap pre-check (added as an extra conjunct to a length formula) that can
         * prune branches where the length/regex constraints on x already make the to_int(x) result impossible to
         * satisfy some arithmetic constraint, without needing to noodlify/split x or enumerate its language.
         *
         * The returned lower bound is always a sound lower bound on to_int(x) (i.e., -1 if x's language may be
         * empty or contain a non-digit symbol, 0 otherwise, possibly tightened further). The returned upper bound
         * (if present) is a sound upper bound; if we cannot establish a finite upper bound (e.g. the digit language
         * is infinite and might represent arbitrarily large numbers), std::nullopt is returned instead, meaning "no
         * known finite upper bound".
         *
         * @param aut_ass Automata assignment giving the language of @p x (and the alphabet used for complementing)
         * @param x The (unflattened, top-level) string variable occurring in "i = str.to_int(x)"
         */
        static std::pair<rational, std::optional<rational>> get_to_int_value_bounds(const AutAssignment& aut_ass, const BasicTerm& x);

        /**
         * @brief Get a LenNode formula conjoining sound bounds (see get_to_int_value_bounds) on the result of
         * every TO_INT conversion in @p conversions, using the languages of the string variables in @p aut_ass.
         *
         * Meant to be conjoined to a length formula as a cheap pre-check, before running the full decision
         * procedure. Returns LenNode(LenFormulaType::TRUE) if there are no TO_INT conversions.
         */
        static LenNode get_to_int_bounds_formula(const AutAssignment& aut_ass, const std::vector<TermConversion>& conversions);
    };
};

#endif
