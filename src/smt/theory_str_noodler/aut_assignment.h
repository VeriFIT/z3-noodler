
#ifndef Z3_STR_AUT_ASSIGNMENT_H_
#define Z3_STR_AUT_ASSIGNMENT_H_

#include <iostream>
#include <map>
#include <set>
#include <queue>
#include <string>
#include <memory>

#include <mata/nfa/nfa.hh>
#include <mata/applications/strings.hh>
#include <mata/nfa/builder.hh>

#include "formula.h"
#include "regex.h"

namespace smt::noodler {

    using IntervalWord = std::vector<std::pair<mata::Symbol,mata::Symbol>>;

    /**
     * hints for using AutAssignment:
     *   - use at() instead of [] operator for getting the value, use [] only for assigning
     *   - if you want to assign some NFA, use std::make_shared<mata::nfa::Nfa>(NFA)
     */
    class AutAssignment : public std::unordered_map<BasicTerm, std::shared_ptr<mata::nfa::Nfa>> {

    private:
        /// Union of all alphabets of automata in the aut assignment
        regex::Alphabet alphabet;

        void update_alphabet() {
            this->alphabet.clear();
            for (const auto& pr : *this) {
                auto alph_symbols = pr.second->alphabet == nullptr ? mata::nfa::create_alphabet(*(pr.second)).get_alphabet_symbols() : pr.second->alphabet->get_alphabet_symbols();
                this->alphabet.insert(alph_symbols.begin(), alph_symbols.end());
            }
        }

    public:
        using std::unordered_map<BasicTerm, std::shared_ptr<mata::nfa::Nfa>>::unordered_map;

        AutAssignment(regex::Alphabet alph) : alphabet(std::move(alph)) { }

        // used for tests, do not use normally
        AutAssignment(std::map<BasicTerm, mata::nfa::Nfa> val) {
            for (const auto &key_value : val) {
                this->operator[](key_value.first) = std::make_shared<mata::nfa::Nfa>(key_value.second);
            }
            update_alphabet();
        };

        static mata::nfa::Nfa empty_string_automaton() {
            return mata::nfa::Nfa(1, {0}, {0});
        }

        mata::nfa::Nfa sigma_star_automaton() const {
            mata::nfa::Nfa nfa{};
            nfa.initial = {0};
            nfa.final = {0};
            for (const mata::Symbol& symb : this->alphabet) {
                nfa.delta.add(0, symb, 0);
            }
            return nfa;
        }

        mata::nfa::Nfa sigma_automaton() const {
            mata::nfa::Nfa nfa{};
            nfa.initial = {0};
            nfa.final = {1};
            for (const mata::Symbol& symb : this->alphabet) {
                nfa.delta.add(0, symb, 1);
            }
            return nfa;
        }

        mata::nfa::Nfa sigma_automaton_of_length(unsigned length) const {
            mata::nfa::Nfa nfa(length+1, {0}, {length});
            for (unsigned i = 0; i < length; ++i) {
                for (const mata::Symbol& symb : this->alphabet) {
                    nfa.delta.add(i, symb, i+1);
                }
            }
            return nfa;
        }

        mata::nfa::Nfa sigma_eps_automaton() const {
            mata::nfa::Nfa nfa{};
            nfa.initial = {0};
            nfa.final = {0,1};
            for (const mata::Symbol& symb : this->alphabet) {
                nfa.delta.add(0, symb, 1);
            }
            return nfa;
        }

        // represents the code point of digit 0
        static constexpr mata::Symbol DIGIT_SYMBOL_START = 48;
        // represents the code point of digit 9
        static constexpr mata::Symbol DIGIT_SYMBOL_END = 57;
        // represents the code point of .
        static constexpr mata::Symbol REAL_NUMBER_DELIMITER = 46;

        /**
         * @brief Returns automaton that accept non-empty words containing only symbols encoding digits (symbols from 48 to 57)
         */
        static mata::nfa::Nfa digit_automaton() {
            mata::nfa::Nfa only_digits_aut(2, {0}, {1});
            for (mata::Symbol digit = DIGIT_SYMBOL_START; digit <= DIGIT_SYMBOL_END; ++digit) {
                only_digits_aut.delta.add(0, digit, 1);
                only_digits_aut.delta.add(1, digit, 1);
            }
            return only_digits_aut;
        }

        /**
         * @brief Returns automaton that accept (possibly empty) words containing only symbols encoding digits (symbols from 48 to 57)
         */
        static mata::nfa::Nfa digit_automaton_with_epsilon() {
            mata::nfa::Nfa only_digits_and_epsilon(1, {0}, {0});
            for (mata::Symbol digit = AutAssignment::DIGIT_SYMBOL_START; digit <= AutAssignment::DIGIT_SYMBOL_END; ++digit) {
                only_digits_and_epsilon.delta.add(0, digit, 0);
            }
            return only_digits_and_epsilon;
        }

        /**
         * @brief Returns automaton that accept words of length @p length containing only symbols encoding digits (symbols from 48 to 57)
         */
        static mata::nfa::Nfa digit_automaton_of_length(unsigned length) {
            mata::nfa::Nfa only_digits_of_length(length+1, {0}, {length});
            for (unsigned i = 0; i < length; ++i) {
                for (mata::Symbol digit = AutAssignment::DIGIT_SYMBOL_START; digit <= AutAssignment::DIGIT_SYMBOL_END; ++digit) {
                    only_digits_of_length.delta.add(i, digit, i+1);
                }
            }
            return only_digits_of_length;
        }

        /// Returns automaton that accept words from [0-9]*.[0-9]* where . is the decimal separator
        static mata::nfa::Nfa decimal_automaton() {
            mata::nfa::Nfa res(2, {0}, {1});
            for (mata::Symbol digit = AutAssignment::DIGIT_SYMBOL_START; digit <= AutAssignment::DIGIT_SYMBOL_END; ++digit) {
                res.delta.add(0, digit, 0);
                res.delta.add(1, digit, 1);
            }
            res.delta.add(0, AutAssignment::REAL_NUMBER_DELIMITER, 1);
            return res;
        }

        /// Returns automaton that accept words from [0-9]{length_of_whole_part}.[0-9]{length_of_decimal_part} where . is the decimal separator
        static mata::nfa::Nfa decimal_automaton_of_lengths(unsigned length_of_whole_part, unsigned length_of_decimal_part) {
            mata::nfa::Nfa res(length_of_whole_part+length_of_decimal_part+2, {0}, {length_of_whole_part+length_of_decimal_part+1});
            for (unsigned i = 0; i < length_of_whole_part; ++i) {
                for (mata::Symbol digit = AutAssignment::DIGIT_SYMBOL_START; digit <= AutAssignment::DIGIT_SYMBOL_END; ++digit) {
                    res.delta.add(i, digit, i+1);
                }
            }
            res.delta.add(length_of_whole_part, AutAssignment::REAL_NUMBER_DELIMITER, length_of_whole_part+1);
            for (unsigned i = length_of_whole_part+1; i < length_of_whole_part+length_of_decimal_part+1; ++i) {
                for (mata::Symbol digit = AutAssignment::DIGIT_SYMBOL_START; digit <= AutAssignment::DIGIT_SYMBOL_END; ++digit) {
                    res.delta.add(i, digit, i+1);
                }
            }
            return res;
        }

        /**
         * @brief Get the vector of "interval" words accepted by @p aut
         * 
         * Interval word is a vector of mata::Symbol intervals (pairs), for example
         *      {[4-10], [11-20], [0-100]}
         * represents all words
         *      {4, 11, 0}
         *      {4, 11, 1}
         *          ...
         *      {4, 12, 2}
         *          ...
         * 
         * Assumes that @p aut is minimized and accepts a non-empty finite language where each word has the same length
         * 
         * @param aut - minimized automaton that accepts finite language where each word has the same length
         */
        static std::vector<IntervalWord> get_interval_words(const mata::nfa::Nfa& aut);

        /**
         * @brief Checks if @p aut encodes literal, i.e., it accepts only one word that does not contain dummy symbol.
         * 
         * Works only if @p aut was trimmed and reduced by simulation (or determinized and minimized).
         * The found literal is saved in @p found_literal.
         */
        static bool aut_encodes_literal(const mata::nfa::Nfa& aut, zstring& found_literal);

        mata::nfa::Nfa get_automaton_concat(const std::vector<BasicTerm>& concat) const {
            mata::nfa::Nfa ret = mata::nfa::builder::create_empty_string_nfa();
            for(const BasicTerm& t : concat) {
                ret = mata::nfa::concatenate(ret, *(this->at(t)));  // fails when not found
            }
            return ret;
        }

        /**
         * @brief Checks if the automaton for @p t is equal to language containing only empty word.
         */
        bool is_epsilon(const BasicTerm &t) const {
            return mata::applications::strings::is_lang_eps(*(this->at(t)));
        }

        /**
         * @brief Checks if the automaton for @p t contains empty word in its language.
         */
        bool contains_epsilon(const BasicTerm &t) const {
            return this->at(t)->is_in_lang(mata::Word{});
        }

        // adds all mappings of variables from other to this assignment except those which already exists in this assignment
        // i.e. if this[var] exists, then nothing happens for var, if it does not, then this[var] = other[var]
        // TODO: probably this is the same as just doing this->insert(other.begin(), other.end())
        // TODO: or even better, if we do not care what happens with other, we can use this->merge(other)
        void add_to_assignment(const AutAssignment &other) {
            for (const auto &it : other) {
                if (this->count(it.first) == 0) {
                    (*this)[it.first] = it.second;
                }
            }
        }

        const regex::Alphabet& get_alphabet() const {
            return this->alphabet;
        }

        void set_alphabet(regex::Alphabet alph) {
            this->alphabet = std::move(alph);
        }

        void add_symbol_to_alphabet(mata::Symbol s) {
            this->alphabet.insert(s);
        }

        bool replace_dummy_with_symbols(std::set<mata::Symbol> symbols);

        /**
         * @brief Replace dummy symbol in all automata by a new symbol
         * 
         * @return The new symbol if there was some dummy symbol to replace
         */
        std::optional<mata::Symbol> replace_dummy_with_new_symbol();

        /**
         * @brief Is language complement of a finite language?
         * 
         * @param t Variable whose language to be checked
         * @return true Is complement of a finite language
         */
        bool is_co_finite(const BasicTerm& t) const {
            mata::nfa::Nfa cmp = mata::nfa::minimize(mata::nfa::complement(*(*this).at(t), alphabet.get_mata_alphabet()));
            return cmp.trim().is_acyclic();
        }

        /**
         * @brief Check if the automaton for @p t accepts only a single word.
         * 
         * It is only underapproximation, as is_singleton is false for the NFA p1 -a-> p2, q1 -a-> q2 where
         * p1, q1 are initial and p2, q2 are final. To get precise information, you determinization+minimization
         * might be necessary, which is often expensive.
         * 
         * @param t Variable
         * @return True -> is surely singleton, False -> inconclusive
         */
        bool is_singleton(const BasicTerm& t) const {
            mata::nfa::Nfa aut = *this->at(t);
            aut.trim();
            return aut.num_of_states() == aut.delta.num_of_transitions() + 1 && aut.initial.size() == 1 && aut.final.size() == 1;
        }

        /**
         * @brief Check if automaton of the @p t is equivalent to the NFA @p aut
         * 
         * @param t Variable
         * @param aut NFA to be compared
         * @return true <-> L(t) = L(aut)
         */
        bool are_equivalent(const BasicTerm& t, const mata::nfa::Nfa& aut) const {
            return mata::nfa::are_equivalent(*this->at(t), aut);
        }

        /**
         * @brief Check if the given terms have disjoint languages.
         * 
         * @param t1 First term
         * @param t2 Second term
         * @return true <-> L(t1) and L(t2) are disjoint.
         */
        bool are_disjoint(const BasicTerm &t1, const BasicTerm& t2) const {
            mata::nfa::Nfa aut_t1 = *this->at(t1);
            mata::nfa::Nfa aut_t2 = *this->at(t2);
            return  mata::nfa::intersection(aut_t1, aut_t2).is_lang_empty();
        }

        /**
         * @brief Check if the language of the basic term has a fixed length
         * 
         * @param t BasicTerm
         * @param n[out] fixed length
         * @return True->fixed length
         */
        bool fixed_length(const BasicTerm& t, int& n) const {
            auto lengths = mata::applications::strings::get_word_lengths(*this->at(t));
            if(lengths.size() != 1) {
                return false;
            }
            auto pr = *lengths.begin();
            n = pr.first;
            return pr.second == 0;
        }

        /**
         * @brief Check if all automata in the map have non-empty language.
         *
         * @return true All have non-empty language
         * @return false There is at least one NFA with the empty language
         */
        bool is_sat() const {
            for (const auto& pr : *this) {
                if(pr.second->final.size() == 0) {
                    return false;
                }
                if(pr.second->is_lang_empty())
                    return false;
            }
            return true;
        }

        /**
         * @brief Reduce all automata occurring in the map.
         */
        void reduce() {
             for (auto& pr : *this) {
                pr.second = std::make_shared<mata::nfa::Nfa>(mata::nfa::reduce(*pr.second));
            }
        }

        /**
         * @brief Get all keys from the assignment
         * 
         * @return std::unordered_set<BasicTerm> Keys
         */
        std::unordered_set<BasicTerm> get_keys() const {
            std::unordered_set<BasicTerm> ret;
            for(const auto & pr : *this) {
                ret.insert(pr.first);
            }
            return ret;
        }

        std::string print() const {
            std::stringstream res;
            for (const auto &key_val : *this) {
                res << "Automaton for " << key_val.first.get_name() << ":" << std::endl << *key_val.second;
            }
            return res.str();
        }

        /**
         * @brief Restrict language of the given basic term @p t by @p restr_nfa.  
         * 
         * @param t Basic term to be restricted
         * @param restr_nfa Language restriction represented by an NFA.
         */
        void restrict_lang(const BasicTerm& t, const mata::nfa::Nfa& restr_nfa) {
            (*this)[t] = std::make_shared<mata::nfa::Nfa>(mata::nfa::intersection(restr_nfa, *this->at(t)));
        }

        /**
         * @brief Get the length formula representing all possible lengths of the automaton for @p var
         */
        LenNode get_lengths(const BasicTerm& var) const;

        /**
         * @brief Get the lengths formula representing all possible lengths of the automaton for @p var and corresponding NFA @p aut.
         */
        static LenNode get_lengths(const mata::nfa::Nfa& aut, const BasicTerm& var);

        /**
         * Create NFA accepting a word in Z3 zstring representation.
         * @param word Word to accept.
         * @return NFA.
         */
        static mata::nfa::Nfa create_word_nfa(const zstring& word);

        /**
         * @brief Complement the given automaton wrt the alphabet induced by the AutAssignment.
         * 
         * @param aut Automaton to be complemented
         * @return mata::nfa::Nfa 
         */
        mata::nfa::Nfa complement_aut(const mata::nfa::Nfa& aut) const {
            return mata::nfa::complement(aut, alphabet.get_mata_alphabet());
        }

        /**
         * @brief Get complement of the term language wrt the alphabet induced by the AutAssignment. 
         * 
         * @param t Term 
         * @return mata::nfa::Nfa 
         */
        mata::nfa::Nfa complement_lang(const BasicTerm& t) {
            return complement_aut(*(this->at(t)));
        }

        /**
         * @brief Check if the automaton corresponding to @p t is flat.
         * Flat automaton is an NFA whose every SCC is a simple loop. Basically each state in an
         * SCC has at most one successor within this SCC.
         *
         * @param t Term
         * @return true <-> the corresponding automaton is flat
         */
        bool is_flat(const BasicTerm& t) const;

        /**
         * @brief If the language of @p t is of the form w* for some non-empty word w,
         * return the base word w; otherwise return std::nullopt.
         *
         * Minimizes and trims the automaton for @p t, then checks whether it is a simple
         * cycle whose unique initial state is also the unique final state.  If so, the
         * symbols along the cycle give the base word w.
         *
         * @param t Term
         * @return The base word w such that L(t) = w*, or std::nullopt if not applicable.
         */
        std::optional<mata::Word> get_word_power_base(const BasicTerm& t) const;

        /**
         * @brief Check if the language of @p t is of the form w* for some non-empty word w.
         *
         * @param t Term
         * @return true iff L(t) = w* for some non-empty word w
         */
        bool is_lang_word_power(const BasicTerm& t) const { return get_word_power_base(t).has_value(); }

    };

} // Namespace smt::noodler.

#endif //Z3_STR_AUT_ASSIGNMENT_H_
