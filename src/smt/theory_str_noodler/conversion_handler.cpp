#include <numeric> 

#include "conversion_handler.h"

namespace smt::noodler {

void ConversionHandler::initialize_solution(SolvingState solution) {
    conversions = solution.conversions;
    this->solution = std::move(solution);

    code_subst_vars.clear();
    int_subst_vars.clear();
    real_subst_vars.clear();
    for (const TermConversion& conv : conversions) {
        switch (conv.type)
        {
            case ConversionType::FROM_CODE:
            case ConversionType::TO_CODE:
            {
                for (const BasicTerm& var : this->solution.get_substituted_vars(conv.string_var)) {
                    code_subst_vars.insert(var);
                }
                break;
            }
            case ConversionType::TO_INT:
            case ConversionType::FROM_INT:
            {
                for (const BasicTerm& var : this->solution.get_substituted_vars(conv.string_var)) {
                    int_subst_vars.insert(var);
                }
                break;
            }
            case ConversionType::TO_REAL:
            case ConversionType::FROM_REAL:
            {
                for (const BasicTerm& var : this->solution.get_substituted_vars(conv.string_var)) {
                    real_subst_vars.insert(var);
                }
                break;
            }
            default:
                UNREACHABLE();
        }
    }

    contain_non_digit = this->solution.aut_ass.complement_aut(only_digits);
    STRACE(str_conversion_int, tout << "only-digit NFA:" << std::endl << only_digits << std::endl;);
    STRACE(str_conversion_int, tout << "contains-non-digit NFA:" << std::endl << contain_non_digit << std::endl;);
    non_number = this->solution.aut_ass.complement_aut(mata::nfa::union_nondet(only_digits, real_numbers));
    STRACE(str_conversion_int, tout << "real-number NFA:" << std::endl << real_numbers << std::endl;);
    STRACE(str_conversion_int, tout << "non-number NFA:" << std::endl << non_number << std::endl;);
}

LenNode ConversionHandler::get_formula_for_code_subst_var(const BasicTerm& code_subst_var) {
    SASSERT(is_var_code_subst_var(code_subst_var));

    // for the code substituting variable c, create the formula
    //   (|c| != 1 && code_version_of(c) == -1) || (|c| == 1 && code_version_of(c) is code point of one of the chars in the language of automaton for c)

    // non_char_case = (|c| != 1 && code_version_of(c) == -1)
    LenNode non_char_case(LenFormulaType::AND, { {LenFormulaType::NEQ, std::vector<LenNode>{code_subst_var, 1}}, {LenFormulaType::EQ, std::vector<LenNode>{code_version_of(code_subst_var),-1}} });

    // char_case = (|c| == 1 && code_version_of(c) is code point of one of the chars in the language of automaton for c)
    LenNode char_case(LenFormulaType::AND, { {LenFormulaType::EQ, std::vector<LenNode>{code_subst_var, 1}}, /* code_version_of(c) is code point of one of the chars in the language of automaton for c */ });

    // the rest is just computing 'code_version_of(c) is code point of one of the chars in the language of automaton for c'

    // chars in the language of c (except dummy symbol)
    std::set<mata::Symbol> real_symbols_of_code_var;
    bool is_there_dummy_symbol = false;
    for (mata::Symbol s : mata::applications::strings::get_accepted_symbols(*solution.aut_ass.at(code_subst_var))) { // iterate trough chars of c
        if (!util::is_dummy_symbol(s)) {
            real_symbols_of_code_var.insert(s);
        } else {
            is_there_dummy_symbol = true;
        }
    }

    if (!is_there_dummy_symbol) {
        // if there is no dummy symbol, we can just create disjunction that code_version_of(c) is equal to one of the symbols in real_symbols_of_code_var
        std::vector<LenNode> equal_to_one_of_symbols;
        for (mata::Symbol s : real_symbols_of_code_var) {
            equal_to_one_of_symbols.emplace_back(LenFormulaType::EQ, std::vector<LenNode>{code_version_of(code_subst_var), s});
        }
        char_case.succ.emplace_back(LenFormulaType::OR, equal_to_one_of_symbols);
    } else {
        // if there is dummy symbol, then code_version_of(c) can be code point of any char, except those in the alphabet but not in real_symbols_of_code_var

        // code_version_of(c) is valid code_point: (0 <= code_version_of(c) <= max_char)
        char_case.succ.emplace_back(LenFormulaType::LEQ, std::vector<LenNode>{0, code_version_of(code_subst_var)});
        char_case.succ.emplace_back(LenFormulaType::LEQ, std::vector<LenNode>{code_version_of(code_subst_var), zstring::max_char()});

        // code_version_of(c) is not equal to code point of some symbol in the alphabet that is not in real_symbols_of_code_var
        for (mata::Symbol s : solution.aut_ass.get_alphabet()) {
            if (!util::is_dummy_symbol(s) && !real_symbols_of_code_var.contains(s)) {
                char_case.succ.emplace_back(LenFormulaType::NEQ, std::vector<LenNode>{code_version_of(code_subst_var), s});
            }
        }
    }

    return LenNode(LenFormulaType::OR, { non_char_case, char_case });
}

LenNode ConversionHandler::encode_interval_words(const BasicTerm& var, const std::vector<IntervalWord>& interval_words) {
    LenNode result(LenFormulaType::OR);
    for (const IntervalWord& interval_word : interval_words) {
        // How this works on an example:
        //      interval_word = [4-5][0-9][2-5][0-9][0-9]
        // We need to encode, as succintcly as possible, that var is any number from the interval word.
        // It is easy to see, that because last two positions can use all digits, we can create following inequations:
        //      ..200 <= var <= ..599
        // where the first two digits are any of [4-5] and [0-9] respectively, i.e., the full encoding should be the
        // following disjunct:
        //      40200 <= var <= 40599 ||
        //      41200 <= var <= 41599 ||
        //               ...
        //      49200 <= var <= 49599 ||
        //      50200 <= var <= 50599 ||
        //      51200 <= var <= 51599 ||
        //               ...
        //      59200 <= var <= 59599

        // We first compute the vector interval_cases of all the intervals [40200-40599], [41200-41599], ...
        // by going backwards in the interval_word, first by computing the main interval [..200-..599] which
        // ends after hitting first digit interval that does not contain all digits (in the exmaple it is [2-5])
        // and after that point, we add all the possible cases for all digits in the following digit intervals.
        std::vector<std::pair<rational,rational>> interval_cases = { {rational(0),rational(0)} }; // start with interval [0-0]
        rational place_value(1); // which point in the interval_word we are now (ones, tens, hundreds, etc.)
        bool need_to_split = false; // have we hit the digit interval that does not contain all digits yet?
        for (auto interval_it = interval_word.crbegin(); interval_it != interval_word.crend(); ++interval_it) { // going backwards in interval_word
            // we are processing interval [s-e]
            rational interval_start(interval_it->first - AutAssignment::DIGIT_SYMBOL_START);
            rational interval_end(interval_it->second - AutAssignment::DIGIT_SYMBOL_START);

            if (!need_to_split) {
                // We are in the situation that all digit intervals after the currently processed one are in the form [0-9], i.e., we have
                //      ...[s-e][0-9]...[0-9]
                // Therefore, we should have only one interval of the form [0...0-9...9] in interval_cases
                assert(interval_cases.size() == 1);
                // We change this interval into [s0...0-e9...9]
                interval_cases[0].first += interval_start*place_value;
                interval_cases[0].second += interval_end*place_value;
                if (interval_start != 0 || interval_end != 9) {
                    // If the currently processed interval is not of the form [0-9], we will have to add all cases for
                    need_to_split = true;
                }
            } else {
                // At least one of the digit intervals after the currently processed one is not in the form [0-9],
                // so for each interval [S-E] in interval_cases and each digit d, s<=d<=e, we need to add interval
                // [dS-dE] to the new vector of interval_cases.
                std::vector<std::pair<rational,rational>> new_interval_cases;
                for (std::pair<rational,rational>& interval_case : interval_cases) {
                    // for each interval [S-E] in interval_cases
                    for (rational possible_digit = interval_start; possible_digit <= interval_end; ++possible_digit) {
                        // for each digit d, s<=d<=e
                        new_interval_cases.push_back({
                            // add [dS-dE] to new_interval_cases
                            possible_digit*place_value + interval_case.first,
                            possible_digit*place_value + interval_case.second
                        });
                    }
                }
                interval_cases = new_interval_cases;
            }

            // move to the following place value (from ones to tens, from tens to hundreds, etc.)
            place_value *= 10;
        }

        // After computing the vector interval_cases, we can just now create the inequalities
        for (const auto& interval_case : interval_cases) {
            rational min = interval_case.first;
            rational max = interval_case.second;
            // we want to put
            //      min <= var <= max
            // but for the special case where min==max, we can just put
            //      var = min (= max)
            if (min == max) {
                result.succ.emplace_back(LenFormulaType::EQ, std::vector<LenNode>{var, min});
            } else {
                result.succ.emplace_back(LenFormulaType::AND, std::vector<LenNode>{
                    LenNode(LenFormulaType::LEQ, {min, var}),
                    LenNode(LenFormulaType::LEQ, {var, max})
                });
            }
        }
    }
    return result;
}

LenNode ConversionHandler::get_formula_for_invalid_case(const BasicTerm& int_real_subst_var) {
    SASSERT(is_var_int_subst_var(int_real_subst_var) || is_var_real_subst_var(int_real_subst_var));

    // part representing invalid cases (for int vars it contains some non-digit, for real vars it is not any number)
    mata::nfa::Nfa aut_non_valid_part = mata::nfa::reduce(mata::nfa::intersection(*solution.aut_ass.at(int_real_subst_var), (is_var_real_subst_var(int_real_subst_var) ? non_number : contain_non_digit)).trim());
    STRACE(str_conversion_int, tout << "non-valid NFA for " << int_real_subst_var << ":" << std::endl << aut_non_valid_part << std::endl;);

    if (aut_non_valid_part.is_lang_empty()) {
        return LenNode(LenFormulaType::FALSE);
    }

    // we create the following formula:
    //       |int_real_subst_var| is length of some word from aut_non_valid_part && int_version_of(int_real_subst_var) = -1 (&& dot_position(int_real_subst_var) = -1)
    // where the part in parentheses is done only for real vars
    LenNode formula_for_non_valid_part(LenFormulaType::AND);
    formula_for_non_valid_part.succ.push_back(solution.aut_ass.get_lengths(aut_non_valid_part, int_real_subst_var)); // |int_real_subst_var| is length of some word from aut_non_valid_part
    formula_for_non_valid_part.succ.emplace_back(LenFormulaType::EQ, std::vector<LenNode>{ int_version_of(int_real_subst_var), -1 }); // int_version_of(int_real_subst_var) = -1
    if (is_var_real_subst_var(int_real_subst_var)) { formula_for_non_valid_part.succ.emplace_back(LenFormulaType::EQ, std::vector<LenNode>{ dot_position_of(int_real_subst_var), -1 }); } // dot_position(int_real_subst_var) = -1

    // if int_real_subst_var is used in some to_code/from_code, we also need to encode that the code_value must be non_valid number
    if (is_var_code_subst_var(int_real_subst_var)) {
        // => we need to add the fact, that int_real_subst_var cannot encode code point of a digit
        //      .. && (code_version_of(int_real_subst_var) < AutAssignment::DIGIT_SYMBOL_START || AutAssignment::DIGIT_SYMBOL_END < code_version_of(int_real_subst_var))
        formula_for_non_valid_part.succ.emplace_back(LenFormulaType::OR, std::vector<LenNode>{
            LenNode(LenFormulaType::LT, { code_version_of(int_real_subst_var), AutAssignment::DIGIT_SYMBOL_START }),
            LenNode(LenFormulaType::LT, { AutAssignment::DIGIT_SYMBOL_END, code_version_of(int_real_subst_var) })
        });
        if (real_subst_vars.contains(int_real_subst_var)) {
            // and for real subst vars, it also cannot encode '.', as for us, this is valid real number (for substituting variable)
            //      .. && code_version_of(int_real_subst_var) != AutAssignment::REAL_NUMBER_DELIMITER
            formula_for_non_valid_part.succ.emplace_back(LenFormulaType::NEQ, std::vector<LenNode>{ code_version_of(int_real_subst_var), AutAssignment::REAL_NUMBER_DELIMITER });
        }
    }
    return formula_for_non_valid_part;
}


LenNode ConversionHandler::get_formula_for_valid_int_case(const BasicTerm& int_real_subst_var, LenNodePrecision& precision) {
    SASSERT(is_var_int_subst_var(int_real_subst_var) || is_var_real_subst_var(int_real_subst_var));
    
    // part containing only digits (i.e. valid int number)
    mata::nfa::Nfa aut_valid_int_part = mata::nfa::reduce(mata::nfa::intersection(*solution.aut_ass.at(int_real_subst_var), only_digits).trim());
    STRACE(str_conversion_int, tout << "valid-int NFA for " << int_real_subst_var << ":" << std::endl << aut_valid_int_part << std::endl;);

    if (aut_valid_int_part.is_lang_empty()) {
        return LenNode(LenFormulaType::FALSE);
    }

    // For each length l of some word containing only digits, we create the formula
    //      |int_real_subst_var| = l && int_version_of(int_real_subst_var) is number represented by some word containing only digits of length l (&& dot_position_of(int_real_subst_var = -1))
    // and add l to int_subst_vars_to_possible_valid_lengths[int_real_subst_var].
    // The part in parentheses is done only if int_real_subst_var is real.
    // Note that for l=0, we set int_version_of(int_real_subst_var) = 0.
    LenNode result(LenFormulaType::OR);

    // maximum length of l
    unsigned max_length_of_words = max_length_of_word_in_aut(aut_valid_int_part, precision);

    // for lengths l=0 to max_length_of_words
    for (unsigned l = 0; l <= max_length_of_words; ++l) {
        // get automaton representing all accepted words containing only digits of length l
        mata::nfa::Nfa aut_valid_of_length = mata::nfa::minimize(mata::nfa::intersection(aut_valid_int_part, AutAssignment::digit_automaton_of_length(l)).trim());

        if (aut_valid_of_length.is_lang_empty()) {
            // there are no such words
            continue;
        }

        // remember that there are some valid words of length l
        int_subst_vars_to_possible_valid_lengths[int_real_subst_var].push_back(l);

        LenNode formula_for_length_l(LenFormulaType::AND);

        // |int_real_subst_var| = l && encode that int_version_of(int_real_subst_var) is a numeral represented by some interval word accepted by aut_valid_of_length
        formula_for_length_l.succ.emplace_back(LenFormulaType::EQ, std::vector<LenNode>{ int_real_subst_var, l });
        formula_for_length_l.succ.push_back(encode_interval_words(int_version_of(int_real_subst_var), AutAssignment::get_interval_words(aut_valid_of_length)));

        if (code_subst_vars.contains(int_real_subst_var) && l == 1) {
            // int_real_subst_var is used in some to_code/from_code AND we are handling the case of l==1 (for other lengths, the formula from get_formula_for_code_subst_vars should force that code_version_of(int_real_subst_var) is -1)
            // => we need to connect code_version_of(int_real_subst_var) and int_version_of(int_real_subst_var)
            //      code_version_of(int_real_subst_var) = int_version_of(int_real_subst_var) + AutAssignment::DIGIT_SYMBOL_START
            formula_for_length_l.succ.emplace_back(LenFormulaType::EQ, std::vector<LenNode>{
                code_version_of(int_real_subst_var),
                LenNode(LenFormulaType::PLUS, std::vector<LenNode>{int_version_of(int_real_subst_var), AutAssignment::DIGIT_SYMBOL_START })
            });
        }

        if (is_var_real_subst_var(int_real_subst_var)) {
            // if int_real_subst_var represents integer, then there is no decimal separator => dot_position_of(int_real_subst_var) = -1
            formula_for_length_l.succ.emplace_back(LenFormulaType::EQ, std::vector<LenNode>{ dot_position_of(int_real_subst_var), -1 });
        }

        result.succ.push_back(formula_for_length_l);
    }
    
    return result;
}

LenNode ConversionHandler::get_formula_for_valid_real_case(const BasicTerm& int_real_subst_var, LenNodePrecision& precision) {
    SASSERT(is_var_real_subst_var(int_real_subst_var));

    // part containing words representing real numbers, i.e. [0-9]*.[0-9]*
    mata::nfa::Nfa aut_valid_real_part = mata::nfa::reduce(mata::nfa::intersection(*solution.aut_ass.at(int_real_subst_var), real_numbers).trim());
    STRACE(str_conversion_int, tout << "valid-real NFA for " << int_real_subst_var << ":" << std::endl << aut_valid_real_part << std::endl;);

    if (aut_valid_real_part.is_lang_empty()) {
        return LenNode(LenFormulaType::FALSE);
    }

    // For each pair <l_w, l_d> of lengths of some word representing real number, where l_w is the length of the whole part (before the eparator) and l_d is the length of 
    // the decimal part (after the separator) we create the formula
    //      |int_real_subst_var| = l_w+1+l_d && dot_position_of(int_real_subst_var = l_w && int_version_of(int_real_subst_var) = -1 
    //                && whole_part_of(int_real_subst_var) is the number representing the whole part
    //                && decimal_part_of(int_real_subst_var) is the number representing the decimal part
    // We also add <l_w+1+l_d, l_w> to real_subst_vars_to_possible_valid_lengths_and_dot_positions[int_real_subst_var].
    // Note that for l_w = 0, we set whole_part_of(int_real_subst_var) = 0 (similarly for l_d = 0).
    LenNode result(LenFormulaType::OR);

    // for each transition s-.->t we keep s in delimiter_source_states and t in delimiter_target_states
    mata::utils::SparseSet<mata::nfa::State> delimiter_source_states;
    mata::utils::SparseSet<mata::nfa::State> delimiter_target_states;
    for (const mata::nfa::Transition& transition : aut_valid_real_part.delta.transitions()) {
        if (transition.symbol == AutAssignment::REAL_NUMBER_DELIMITER) {
            delimiter_source_states.insert(transition.source);
            delimiter_target_states.insert(transition.target);
        }
    }

    unsigned max_length_of_whole_part, max_length_of_decimal_part;

    // part of aut accepting languages up to '.' (the whole part of the numbers)
    mata::nfa::Nfa aut_delimiter_part = aut_valid_real_part;
    aut_delimiter_part.final = delimiter_source_states;
    aut_delimiter_part.trim();
    STRACE(str_conversion_int, tout << "whole part of valid-real NFA for " << int_real_subst_var << ":" << std::endl << aut_delimiter_part << std::endl;);
    max_length_of_whole_part = max_length_of_word_in_aut(aut_delimiter_part, precision);

    // part of aut accepting languages from '.' (the decimal part of the numbers)
    aut_delimiter_part = aut_valid_real_part;
    aut_delimiter_part.initial = delimiter_target_states;
    aut_delimiter_part.trim();
    STRACE(str_conversion_int, tout << "decimal part of valid-real NFA for " << int_real_subst_var << ":" << std::endl << aut_delimiter_part << std::endl;);
    max_length_of_decimal_part = max_length_of_word_in_aut(aut_delimiter_part, precision);

    for (unsigned whole_length = 0; whole_length <= max_length_of_whole_part; ++whole_length) {
        for (unsigned decimal_length = 0; decimal_length <= max_length_of_decimal_part; ++decimal_length) {
            // get automaton representing all accepted words whose whole part has length whole_length and decimal part has length decimal_length
            mata::nfa::Nfa aut_valid_of_length = mata::nfa::minimize(mata::nfa::intersection(aut_valid_real_part, AutAssignment::decimal_automaton_of_lengths(whole_length, decimal_length)).trim());

            if (aut_valid_of_length.is_lang_empty()) {
                // there are no such words
                continue;
            }

            STRACE(str_conversion_int, tout << "valid-real NFA with whole length " << whole_length << " and decimal length " << decimal_length <<":" << std::endl << aut_valid_of_length << std::endl;);

            // the current length of the whole word (whole part + decimal separator + decimal part)
            unsigned length_of_number = whole_length + 1 + decimal_length;

            // remember the current length of the whole word and the position of the decimal separator
            real_subst_vars_to_possible_valid_lengths_and_dot_positions[int_real_subst_var].emplace_back(length_of_number, whole_length);

            LenNode formula_for_cur_lengths(LenFormulaType::AND);

            // |int_real_subst_var| = length_of_number && dot_position_of(int_real_subst_var) is the position of decimal separator && int_version_of(int_real_subst_var) = -1 && whole_part_of(int_real_subst_var) and decimal_part_of(int_real_subst_var) are numerals represented by some interval word accepted by corresponding part of aut_valid_of_length
            formula_for_cur_lengths.succ.emplace_back(LenFormulaType::EQ, std::vector<LenNode>{ int_real_subst_var, length_of_number }); // |int_real_subst_var| = length_of_number
            formula_for_cur_lengths.succ.emplace_back(LenFormulaType::EQ, std::vector<LenNode>{ dot_position_of(int_real_subst_var), whole_length }); // dot_position_of(int_real_subst_var) is the position of decimal separator
            formula_for_cur_lengths.succ.emplace_back(LenFormulaType::EQ, std::vector<LenNode>{ int_version_of(int_real_subst_var), -1 }); // int_version_of(int_real_subst_var) = -1, because we have '.', so we cannot have integer number

            LenNode formula_for_interval_words(LenFormulaType::OR);
            for (const IntervalWord& interval_word : AutAssignment::get_interval_words(aut_valid_of_length)) {
                // each interval word of aut_valid_of_length should be split on the delimiter, i.e. the position of delimiter in interval_word will have the interval ['.', '.']
                SASSERT((interval_word[whole_length] == std::pair{ AutAssignment::REAL_NUMBER_DELIMITER, AutAssignment::REAL_NUMBER_DELIMITER }));
                IntervalWord whole_part_interval_word(interval_word.begin(), interval_word.begin()+whole_length); // the interval word before the separator
                IntervalWord decimal_part_interval_word(interval_word.begin()+whole_length+1, interval_word.end()); // the interval word after the separator
                formula_for_interval_words.succ.emplace_back(LenFormulaType::AND, std::vector<LenNode>{
                    encode_interval_words(whole_part_of(int_real_subst_var), { whole_part_interval_word }),
                    encode_interval_words(decimal_part_of(int_real_subst_var), { decimal_part_interval_word })
                });
            }
            formula_for_cur_lengths.succ.push_back(formula_for_interval_words);

            if (is_var_code_subst_var(int_real_subst_var) && length_of_number == 1) {
                // int_real_subst_var is used in some to_code/from_code AND because we have both whole and decimal parts empty, we are handling the case where we have the only word "."
                // => we need to put code_version_of(int_real_subst_var) == code point of '.'
                formula_for_cur_lengths.succ.emplace_back(LenFormulaType::EQ, std::vector<LenNode>{ code_version_of(int_real_subst_var), AutAssignment::REAL_NUMBER_DELIMITER });
            }

            result.succ.push_back(formula_for_cur_lengths);
        }
    }

    return result;
}

std::pair<LenNode, LenNodePrecision> ConversionHandler::get_formula_for_int_real_subst_var(const BasicTerm& int_real_subst_var) {
    SASSERT(is_var_int_subst_var(int_real_subst_var) || is_var_real_subst_var(int_real_subst_var));
    STRACE(str_conversion_int, tout << "NFA for " << int_real_subst_var << ":" << std::endl << *solution.aut_ass.at(int_real_subst_var) << std::endl;);

    LenNode result(LenFormulaType::AND);
    LenNodePrecision res_precision = LenNodePrecision::PRECISE;

    LenNode formula_for_int_real_subst_var(LenFormulaType::OR);

    // Add the case that do not represent numbers
    formula_for_int_real_subst_var.succ.push_back(get_formula_for_invalid_case(int_real_subst_var));

    // Add the case encoding integers
    int_subst_vars_to_possible_valid_lengths[int_real_subst_var] = {};
    formula_for_int_real_subst_var.succ.push_back(get_formula_for_valid_int_case(int_real_subst_var, res_precision));

    // Add the case encoding real numbers
    if (is_var_real_subst_var(int_real_subst_var)) {
        real_subst_vars_to_possible_valid_lengths_and_dot_positions[int_real_subst_var] = {};
        formula_for_int_real_subst_var.succ.push_back(get_formula_for_valid_real_case(int_real_subst_var, res_precision));

        // We also add the formula
        //     dot_position_of(int_real_subst_var) == -1 => (whole_part_of(int_real_subst_var) == -1 && whole_part_of(int_real_subst_var) == -1)
        // The formula is actually not needed (if dot position is -1 we do not touch the whole/decimal parts). However, it is important to define
        // the variables for the parts somewhere, for model generation, otherwise Z3 would not know they exist.
        formula_for_int_real_subst_var = LenNode(LenFormulaType::AND, {
            formula_for_int_real_subst_var,
            LenNode(LenFormulaType::OR, {
                LenNode(LenFormulaType::NEQ, { dot_position_of(int_real_subst_var), -1 }),
                LenNode(LenFormulaType::AND, {
                    LenNode(LenFormulaType::EQ, { whole_part_of(int_real_subst_var), -1 }),
                    LenNode(LenFormulaType::EQ, { decimal_part_of(int_real_subst_var), -1 }),
                })
            })
        });
    }

    STRACE(str_conversion_int, tout << "int_real_subst_var formula for " << int_real_subst_var << ": " << formula_for_int_real_subst_var << std::endl;);
    return {formula_for_int_real_subst_var, res_precision};
}

LenNode ConversionHandler::get_formula_for_code_conversion(const TermConversion& conv) {
    const BasicTerm& s = conv.string_var;
    const BasicTerm& c = conv.number_var;

    // First handle the invalid inputs
    LenNode invalid_case(LenFormulaType::AND);
    if (conv.type == ConversionType::TO_CODE) {
        // For to_code, invalid input is string whose length is not 1
        // (|s| != 1 && c == -1)
        invalid_case.succ.emplace_back(LenFormulaType::NEQ, std::vector<LenNode>{s, 1});
        invalid_case.succ.emplace_back(LenFormulaType::EQ, std::vector<LenNode>{c, -1});
    } else {
        // For from_code, invalid input is a number not representing a code point of some char
        // (|s| == 0 && c is not a valid code point)
        invalid_case.succ.emplace_back(LenFormulaType::EQ, std::vector<LenNode>{s, 0});
        // non-valid code point means that 'c < 0 || c > max_char'
        invalid_case.succ.emplace_back(LenFormulaType::OR, std::vector<LenNode>{
            LenNode(LenFormulaType::LT, {c, 0}),
            LenNode(LenFormulaType::LT, {zstring::max_char(), c})
        });
    }

    // For s=s_1s_2...s_n substitution in the flattened solution, we now handle the valid inputs:
    //    (|s| == 1 && c >= 0 && c is equal to one of code_version_of(s_i))
    // This is shared for both to_code and from_code.
    LenNode valid_case(LenFormulaType::AND, { {LenFormulaType::EQ, std::vector<LenNode>{s, 1}}, {LenFormulaType::LEQ, std::vector<LenNode>{0, c}}, /*c is equal to one of code_version_of(s_i))*/ });

    // c is equal to one of code_version_of(s_i)
    LenNode equal_to_one_subst_var(LenFormulaType::OR);
    for (const BasicTerm& subst_var : solution.get_substituted_vars(s)) {
        // c == code_version_of(s_i)
        equal_to_one_subst_var.succ.emplace_back(LenFormulaType::EQ, std::vector<LenNode>{c, code_version_of(subst_var)});
    }
    valid_case.succ.push_back(equal_to_one_subst_var);

    return LenNode(LenFormulaType::OR, std::vector<LenNode>{
        invalid_case,
        valid_case
    });
}

LenNode ConversionHandler::get_formula_for_number_conversion(BasicTerm result, const std::vector<BasicTerm>& subst_vars, std::vector<unsigned> lengths_of_subst_vars, std::optional<std::pair<size_t,unsigned>> index_of_subst_var_with_dot_and_dot_position) {
    SASSERT(subst_vars.size() == lengths_of_subst_vars.size());

    // Example:
    //     subst_vars = s0,s1,s2,s3,s4    lengths_of_subst_vars = 2,1,6,0,1    index_of_subst_var_with_dot_and_dot_position=(2,2)
    // We want to encode in result the number represented by s0.s1.s2.s3.s4 for the case that |s0|==2, |s1|==1, |s2|==6, |s3|==0, |s4|==1 and the
    // decimal delimiter is on the second position in s2. Visually
    //
    //         0   1   2   3   4   5   6   7   8   9
    //       |   |   |   |   |   | . |   |   |   |   |
    //       |  s0   | s1|           s2          | s4|
    //
    // We want to encode that positions 0-4 represent the whole number, using int_version_of(s0), int_version_of(s1), and whole_part_of(s2).
    // Furthermore, positions 6-9 encode the decimal number, using decimal_part_of(s2), and int_version_of(s4). We can ignore int_version_of(s3), it is empty.
    // We want to get the sum
    //         result = int_version_of(s0)*1000 + int_version_of(s1)*100 + whole_part_of(s2) + decimal_part_of(s2)*0.001 + int_version_of(s4)*0.0001
    // Note that we always multiply by power of 10. For example, we multiply int_version_of(s0) by 10^3, because |s1|+|whole part of s2| = 3. Similarly,
    // we multiply int_version_of(s4) by 10^-4, because |decimal part of s2|+|s3|+|s4| = 4.
    // For example, if s0="13", s1="4", s2="37.155", s3="", s4="6", the resulting number "13437.1556" can be encoded as the sum
    //          13*1000 + 4*100 + 37 + 155*0.001 + 6*0.0001
    //
    // Furthermore, we need to encode that int_version_of variables s0, s1, s4 are valid integers (they are !=-1), dot_position_of(s2)=2 and lengths
    // of all variables are correct.
    //
    // If index_of_subst_var_with_dot_and_dot_position is not given, we assume the word s0.s1.s2.s3.s4 represents an integer, that is we can assume it is on position 10

    // The resulting formula (both conditions on int_version_of/dot_position_of and the sum)
    LenNode formula_for_case(LenFormulaType::AND);
    // The sum computing the whole number, which we then assign to result
    LenNode formula_for_sum(LenFormulaType::PLUS);

    // Full length of the word s0.s1....sn
    const unsigned FULL_LENGTH = std::accumulate(lengths_of_subst_vars.begin(), lengths_of_subst_vars.end(), 0u);
    if (FULL_LENGTH == 0 || (FULL_LENGTH == 1 && index_of_subst_var_with_dot_and_dot_position.has_value())) {
        // the case where we have empty word, or a word containing only decimal separator is invalid case, therefore we are not encoding a number
        // and can return false
        return LenNode(LenFormulaType::FALSE);
    }

    // We will use the following two numbers to compute 10^... in the sum. There is rational::expt(), but it seems it is very slow/does not work.
    rational place_value_whole_part(1); // we will compute the power of 10 in this number for the whole part
    rational place_value_decimal_part(1); // we will compute the power of 10 in this number for the decimal part

    size_t index_of_dot_subst_var;
    if (index_of_subst_var_with_dot_and_dot_position.has_value()) {
        // First we handle the subst_var that contains decimal delimiter, if it exists (s2 in our example)
        index_of_dot_subst_var = index_of_subst_var_with_dot_and_dot_position.value().first;
        {
            const BasicTerm& dot_subst_var = subst_vars[index_of_dot_subst_var];
            unsigned dot_position_in_dot_subst_var = index_of_subst_var_with_dot_and_dot_position.value().second;
            unsigned length_of_dot_subst_var = lengths_of_subst_vars[index_of_dot_subst_var];
            // We add to the sum
            //       whole_part_of(dot_subst_var) + decimal_part_of(dot_subst_var)*(10^-(length of decimal part of dot_subst_var))
            // where the length of decimal part of dot_subst_var is length_of_dot_subst_var-dot_position_in_dot_subst_var-1
            formula_for_sum.succ.emplace_back(whole_part_of(dot_subst_var));
            for (unsigned i = 0; i < dot_position_in_dot_subst_var; ++i) { place_value_whole_part *= 10; } // update place_value_whole_part for the next subst_var in the whole part
            for (unsigned i = 0; i < length_of_dot_subst_var-dot_position_in_dot_subst_var-1; ++i) { place_value_decimal_part /= 10; } // initialize the correct power of 10 for the decimal part
            formula_for_sum.succ.emplace_back(LenFormulaType::TIMES, std::vector<LenNode>{ decimal_part_of(dot_subst_var), place_value_decimal_part });

            // we also need to give the correct values for |dot_subst_var|, int_var_of(dot_subst_var) and dot_position_of(dot_subst_var)
            formula_for_case.succ.emplace_back(LenFormulaType::EQ, std::vector<LenNode>{ dot_subst_var, length_of_dot_subst_var }); // |dot_subst_var| has correct length
            formula_for_case.succ.emplace_back(LenFormulaType::EQ, std::vector<LenNode>{int_version_of(dot_subst_var), -1}); // int_var_of(dot_subst_var) == -1, because we have dot in dot_subst_var, i.e. we do not have valid integer
            // dot_position_of(dot_subst_var) is the position of decimal separator within subst_var
            formula_for_case.succ.emplace_back(LenFormulaType::EQ, std::vector<LenNode>{dot_position_of(dot_subst_var), dot_position_in_dot_subst_var});

            STRACE(str_conversion_int, tout << "part of valid part after dot subst var for int/real conversion: " << formula_for_case << std::endl;);
            STRACE(str_conversion_int, tout << "part of the sum after dot subst var for int/real conversion: " << formula_for_sum << std::endl;);
        }

        // We continue by constructing the decimal part
        for (size_t i = index_of_dot_subst_var+1; i < subst_vars.size(); ++i) {
            const BasicTerm& decimal_subst_var = subst_vars[i];
            unsigned length_of_decimal_subst_var = lengths_of_subst_vars[i];

            // The decimal_subst_var is fully in the decimal part of the resulting number, we add to the sum
            //        int_version_of(decimal_subst_var)*(10^-(the length of the decimal part before this subst_var + length_of_decimal_subst_var))
            // where we have 10^-(the length of the decimal part before this subst_var) already computed in place_value_decimal_part, we just need to update
            // it by length_of_decimal_subst_var.
            // Note that for |subst_var|==0, we will have int_version_of(subst_var)==0, from get_formula_for_int_real_subst_vars().
            for (unsigned i = 0; i < length_of_decimal_subst_var; ++i) { place_value_decimal_part /= 10; } // update to the correct power of 10 for the decimal part
            formula_for_sum.succ.emplace_back(LenFormulaType::TIMES, std::vector<LenNode>{ int_version_of(decimal_subst_var), place_value_decimal_part });

            // we also need to give the correct values for |decimal_subst_var| and int_var_of(decimal_subst_var)
            formula_for_case.succ.emplace_back(LenFormulaType::EQ, std::vector<LenNode>{ decimal_subst_var, length_of_decimal_subst_var }); // |decimal_subst_var| has correct length
            formula_for_case.succ.emplace_back(LenFormulaType::NEQ, std::vector<LenNode>{int_version_of(decimal_subst_var), -1}); // int_var_of(decimal_subst_var) != -1, we want it to be some integer
            // dot_position_of(decimal_subst_var) is not needed, it should be -1 from the previous disequation (see get_formula_for_int_real_subst_vars())

            STRACE(str_conversion_int, tout << "part of valid part after decimal subst var for int/real conversion: " << formula_for_case << std::endl;);
            STRACE(str_conversion_int, tout << "part of the sum after decimal subst var for int/real conversion: " << formula_for_sum << std::endl;);
        }
    } else {
        // in this case, all subst vars are in the whole part, so we can pretend that the index is in the non-existent subst var after the last var
        index_of_dot_subst_var = subst_vars.size();
    }

    // We continue by constructing the whole part
    size_t i = index_of_dot_subst_var;
    while (i != 0) {
        --i;
        const BasicTerm& whole_subst_var = subst_vars[i];
        unsigned length_of_whole_subst_var = lengths_of_subst_vars[i];

        // The whole_subst_var is fully in the decimal part of the resulting number, we add to the sum
        //        int_version_of(whole_subst_var)*(10^the length of the whole part after this whole_subst_var)
        // where the length of the whole part after this whole_subst_var is already computed in place_value_whole_part.
        // Note that for |whole_subst_var|==0, we will have int_version_of(whole_subst_var)==0, from get_formula_for_int_real_subst_vars().
        formula_for_sum.succ.emplace_back(LenFormulaType::TIMES, std::vector<LenNode>{ int_version_of(whole_subst_var), place_value_whole_part });
        for (unsigned i = 0; i < length_of_whole_subst_var; ++i) { place_value_whole_part *= 10; } // update place_value_whole_part for the next subst_var in the whole part

        // we also need to give the correct values for |whole_subst_var| and int_var_of(whole_subst_var)
        formula_for_case.succ.emplace_back(LenFormulaType::EQ, std::vector<LenNode>{ whole_subst_var, length_of_whole_subst_var }); // |whole_subst_var| has correct length
        formula_for_case.succ.emplace_back(LenFormulaType::NEQ, std::vector<LenNode>{int_version_of(whole_subst_var), -1}); // int_var_of(whole_subst_var) != -1, we want it to be some integer
        // dot_position_of(whole_subst_var) is not needed, it should be -1 from the previous disequation (see get_formula_for_int_real_subst_vars())

        STRACE(str_conversion_int, tout << "part of valid part after whole subst var for int/real conversion: " << formula_for_case << std::endl;);
        STRACE(str_conversion_int, tout << "part of the sum after whole subst var for int/real conversion: " << formula_for_sum << std::endl;);
    }

    formula_for_case.succ.emplace_back(LenFormulaType::EQ, std::vector<LenNode>{ result, formula_for_sum });
    return formula_for_case;
}

LenNode ConversionHandler::get_formula_for_int_real_conversion(const TermConversion& conv) {
    const BasicTerm& s = conv.string_var;
    const BasicTerm& i = conv.number_var;

    LenNode result(LenFormulaType::OR);

    // s = s_1 ... s_n, subst_vars = <s_1, ..., s_n>
    const std::vector<BasicTerm>& subst_vars = solution.get_substituted_vars(s);

    // first handle non-valid cases
    if (conv.type == ConversionType::TO_INT) {
        // for TO_INT empty string or anything that contains non-digit
        LenNode empty_or_one_subst_contains_non_digit(LenFormulaType::OR, {LenNode(LenFormulaType::EQ, {s, 0})}); // start with empty string: |s| = 0

        for (const BasicTerm& subst_var : subst_vars) {
            // subst_var contain non-digit if one of s_i == -1 (see get_formula_for_int_subst_vars)
            empty_or_one_subst_contains_non_digit.succ.emplace_back(LenFormulaType::EQ, std::vector<LenNode>{int_version_of(subst_var), -1});
        }

        result.succ.emplace_back(LenFormulaType::AND, std::vector<LenNode>{
            empty_or_one_subst_contains_non_digit,
            LenNode(LenFormulaType::EQ, {i, -1}) // for non-valid s, to_int(s) == -1
        });
    } else if (conv.type == ConversionType::TO_REAL) {
        // for TO_REAL empty string, string ".", or anything that contains character that is not a digit and neither '.', or string with two '.'
        LenNode invalid_cases(LenFormulaType::OR);
        invalid_cases.succ.emplace_back(LenFormulaType::EQ, std::vector<LenNode>{s, 0}); // |s| = 0

        // one subst_var does not encode number (neither integer nor real number)
        for (const BasicTerm& subst_var : subst_vars) {
            invalid_cases.succ.emplace_back(LenFormulaType::AND, std::vector<LenNode>{
                LenNode(LenFormulaType::EQ, { int_version_of(subst_var), -1 }), // does not encode integer and
                LenNode(LenFormulaType::EQ, { dot_position_of(subst_var), -1 }) // does not encode real number
            });
        }

        // two subst_vars contain decimal separator
        for (size_t i = 0; i < subst_vars.size(); ++i) {
            for (size_t j = i+1; j < subst_vars.size(); ++j) {
                invalid_cases.succ.emplace_back(LenFormulaType::AND, std::vector<LenNode>{
                    LenNode(LenFormulaType::NEQ, { dot_position_of(subst_vars[i]), -1 }), // both subst_vars[i] and
                    LenNode(LenFormulaType::NEQ, { dot_position_of(subst_vars[j]), -1 })  // subst_vars[j] encode real number
                });
            }
        }

        // there is only decimal separator in s (|s| = 1 and some subst_var encodes real number)
        LenNode one_subst_var_is_real(LenFormulaType::OR);
        for (const BasicTerm& subst_var : subst_vars) {
            one_subst_var_is_real.succ.emplace_back(LenFormulaType::NEQ, std::vector<LenNode>{dot_position_of(subst_var), -1 });
        }
        invalid_cases.succ.emplace_back(LenFormulaType::AND, std::vector<LenNode>{
            LenNode(LenFormulaType::EQ, {s, 1}), // |s| = 1
            one_subst_var_is_real
        });

        result.succ.emplace_back(LenFormulaType::AND, std::vector<LenNode>{
            invalid_cases,
            LenNode(LenFormulaType::EQ, {i, -1}) // for non-valid s, to_real(s) == -1
        });
    } else {
        // for FROM_INT/FROM_REAL only empty string is invalid (as we assume that language of s was set to only possible results of from_int/from_real)
        result.succ.emplace_back(LenFormulaType::AND, std::vector<LenNode>{
            LenNode(LenFormulaType::LT, {i, 0}), // from_int(i) = "" or from_real(i) = "" only if i < 0
            LenNode(LenFormulaType::EQ, {s, 0})
        });
    }

    STRACE(str_conversion_int, tout << "non-valid part for int/real conversion: " << result << std::endl;);

    if (subst_vars.size() == 0) {
        // we only have empty word, i.e., a non-valid case that is already in result
        return result;
    }

    bool is_real_conversion = conv.is_real_conversion();

    // This vector will contain the pairs
    //      < <l_1,l_2,...,l_n>, D >
    // Where each l_i is one possible length of some word of s_i representing integer AND if D=<j,d> is defined, then l_j instead is
    // the length of some word w of s_j representing real number with decimal separator on position d in w.
    std::vector<std::pair<std::vector<unsigned>,std::optional<std::pair<size_t,unsigned>>>> length_cases_with_dot_position = {std::pair<std::vector<unsigned>,std::optional<std::pair<size_t,unsigned>>>{{}, std::nullopt}};
    for (size_t i = 0; i < subst_vars.size(); ++i) {
        // length_cases_with_dot_position contains the pairs < <l_1,l_2,..,l_{i-1}>, D>, we are adding l_i to the vector (or possibly new D)
        const BasicTerm& subst_var = subst_vars[i];
        std::vector<std::pair<std::vector<unsigned>,std::optional<std::pair<size_t,unsigned>>>> new_cases;

        // first we add each l_i, the length of some word of s_i representing integer
        const std::vector<unsigned>& possible_lengths = int_subst_vars_to_possible_valid_lengths.at(subst_var);
        for (const std::pair<std::vector<unsigned>,std::optional<std::pair<size_t,unsigned>>>& old_case : length_cases_with_dot_position) {
            for (unsigned possible_length : possible_lengths) {
                std::pair<std::vector<unsigned>,std::optional<std::pair<size_t,unsigned>>> new_case = old_case;
                new_case.first.push_back(possible_length); // add l_i to vector
                new_cases.push_back(new_case);
            }
        }

        // and if we have a real conversion...
        if (is_real_conversion) {
            // ... we add l_i, the length of some word of s_i representing real number
            const std::vector<std::pair<unsigned,unsigned>>& possible_dot_positions = real_subst_vars_to_possible_valid_lengths_and_dot_positions.at(subst_var);
            for (const std::pair<std::vector<unsigned>,std::optional<std::pair<size_t,unsigned>>>& old_case : length_cases_with_dot_position) {
                if (!old_case.second.has_value()) { // but only if there is not already some s_j, j<i, that represents real number
                    for (const auto& [possible_length, dot_position] : possible_dot_positions) {
                        std::pair<std::vector<unsigned>,std::optional<std::pair<size_t,unsigned>>> new_case = old_case;
                        new_case.first.push_back(possible_length); // add l_i to vector
                        new_case.second = std::pair<size_t,unsigned>{ i, dot_position }; // add D=<i, dot_position>
                        new_cases.push_back(new_case);
                    }
                }
            }
        }

        length_cases_with_dot_position = new_cases;
    }

    for (const auto& one_case : length_cases_with_dot_position) {
        if (conv.type != ConversionType::FROM_REAL) {
            result.succ.push_back(get_formula_for_number_conversion(i, subst_vars, one_case.first, one_case.second));
        } else {
            // For from_real, we need to handle it specially, because we have width, the decimal part of the result will be cut.
            // We create helping var that will have the cut value:
            BasicTerm cut_value(BasicTermType::RealVariable, i.get_name() + "!cut_value");
            LenNode formula_for_cut_value = get_formula_for_number_conversion(cut_value, subst_vars, one_case.first, one_case.second);
            // And we need the real value to be between
            //       cut_value <= i < cut_value+10^-width
            rational power_of_ten(1);
            if (!(conv.width).is_unsigned()) { util::throw_error("We cannot handle non-unsigned width for str.to_real"); } // just to be safe
            for (unsigned i = 0; i < conv.width.get_unsigned(); ++i) { power_of_ten /= 10; }
            result.succ.emplace_back(LenFormulaType::AND, std::vector<LenNode>{
                formula_for_cut_value,
                LenNode(LenFormulaType::LEQ, {0, LenNode(LenFormulaType::MINUS, {i, cut_value})}), // we put 0 <= i - cut_value and not i <= cut_value, z3 has problem with it
                LenNode(LenFormulaType::LT, {LenNode(LenFormulaType::MINUS, {i, cut_value}), power_of_ten}) // we put i - cut_value < 10^-width and not i < cut_value+10^-width, z3 has problem with it
            });
        }
    }

    STRACE(str_conversion_int, tout << "int/real conversion: " << result << std::endl;);
    return result;
}

/**
 * Creates a LI(R)A formula that encodes to_code/from_code/to_int/from_int/to_real/from_real functions.
 * Assumes that
 *      - solution is flattened,
 *      - will be used in conjunction with the result of solution.get_lengths(),
 *      - the resulting string variable of from_code/from_int/from_real is restricted to only valid results of from_code/from_int/from_real (should be done in theory_str_noodler::handle_conversion),
 *      - if to_int/from_int/to_real/from_real will be processed, code points of all digits (symbols 48,..,57) should be in the alphabet (should be done in theory_str_noodler::final_check_eh).
 *      - if to_real/from_real will be processed, the decimal separator '.' is in the alphabet (should be done in theory_str_noodler::final_check_eh).
 *
 * We have following types of conversions:
 *      c = to_code(s)
 *      s = from_code(s)
 *      i = to_int(s)
 *      s = from_int(i)
 *      r = to_real(s)
 *      s = from_real(r)
 * With s a string variable, c/i an integer variable, r a real variable.
 * The string variable s can be substituted in the (flattened) solution:
 *      s = s_1 ... s_n (note that we should have |s| = |s_1| + ... + |s_n| from solution.get_lengths())
 * We therefore collect all vars s_i and put them into three sets:
 *      code_subst_vars - all vars that substitute some s in to_code/from_code
 *      int_subst_vars - all vars that substitute some s in to_int/from_int
 *      real_subst_vars - all vars that substitute some s in to_real/from_real
 *
 * We will then use functions get_formula_for_code_subst_vars and get_formula_for_real_int_subst_vars to encode
 *      - for each s \in code_subst_vars a formula compactly saying that
 *          - code_version_of(s) is equal to some to_code(w_s) for any w_s \in solution.aut_ass.at(s) with the condition that |s| == |w_s|
 *      - for each s \in int_subst_vars a formula compactly saying that
 *          - int_version_of(s) is equal to some to_int(w_s) for any w_s \in solution.aut_ass.at(s) with the condition that |s| == |w_s| AND if s also belongs to code_subst_vars, there is a correspondence between int_version_of(s) and code_version_of(s)
 *      - for each s \in real_subst_vars
 *          - the same int_version_of(s) as in previous + dot_position_of(s), whole_part_of(s), and decimal_part_of(s) encoding the parts of decimal numbers w_s \in solution.aut_ass.at(s) with the correspondence with code_version and lengths
 *
 * After that, we use get_formula_for_code_conversion to handle code conversions - both to_code and from_code are handled similarly for valid strings (i.e. strings of length 1), invalid cases must be handled differently.
 * Similarly, we use get_formula_for_int_real_conversion to handle int/real conversions.
 */
std::pair<LenNode, LenNodePrecision> ConversionHandler::get_formula_encoding_conversions(const std::set<BasicTerm> subst_vars_not_needed_to_be_handled) {
    STRACE(str_conversion,
        tout << "Creating formula for conversions" << std::endl;
    );

    // the resulting formula
    LenNode result(LenFormulaType::AND);
    LenNodePrecision res_precision = LenNodePrecision::PRECISE;

    // create formula for each variable substituting some string_var in some code conversion
    for (const BasicTerm& code_subst_var : code_subst_vars) {
        if (!subst_vars_not_needed_to_be_handled.contains(code_subst_var)) {
            result.succ.push_back(get_formula_for_code_subst_var(code_subst_var));
        }
    }

    // create formula for each variable substituting some string_var in some int/real conversion
    int_subst_vars_to_possible_valid_lengths = {};
    real_subst_vars_to_possible_valid_lengths_and_dot_positions = {};
    std::set<BasicTerm> int_real_subst_vars = int_subst_vars;
    int_real_subst_vars.insert(real_subst_vars.begin(), real_subst_vars.end());
    for (const BasicTerm& int_real_subst_var : int_real_subst_vars) {
        if (!subst_vars_not_needed_to_be_handled.contains(int_real_subst_var)) {
            auto [int_real_subst_formula, int_real_subst_formula_precision] = get_formula_for_int_real_subst_var(int_real_subst_var);
            result.succ.push_back(int_real_subst_formula);
            res_precision = get_resulting_precision_for_conjunction(res_precision, int_real_subst_formula_precision);
        }
    }

    for (const TermConversion& conv : conversions) {
        STRACE(str_conversion,
            tout << " processing " << get_conversion_name(conv.type) << " with string var " << conv.string_var << " and number var " << conv.number_var << std::endl;
        );

        switch (conv.type)
        {
            case ConversionType::TO_CODE:
            case ConversionType::FROM_CODE:
            {
                result.succ.push_back(get_formula_for_code_conversion(conv));
                break;
            }
            case ConversionType::TO_INT:
            case ConversionType::FROM_INT:
            case ConversionType::TO_REAL:
            case ConversionType::FROM_REAL:
            {
                result.succ.push_back(get_formula_for_int_real_conversion(conv));
                break;
            }
            default:
                UNREACHABLE();
        }
    }

    if (result.succ.empty()) {
        result = LenNode(LenFormulaType::TRUE);
    }

    STRACE(str_conversion,
        tout << "Formula for conversions: " << result << std::endl;
    );
    return {result, res_precision};
}

std::vector<BasicTerm> ConversionHandler::get_arith_vars_needed_for_model() {
    std::vector<BasicTerm> needed_vars;
    for (const BasicTerm& code_subst_var : code_subst_vars) {
        needed_vars.push_back(code_version_of(code_subst_var));
    }
    for (const BasicTerm& int_subst_var : int_subst_vars) {
        needed_vars.push_back(int_version_of(int_subst_var));
    }
    for (const BasicTerm& real_subst_var : real_subst_vars) {
        needed_vars.push_back(dot_position_of(real_subst_var));
        needed_vars.push_back(whole_part_of(real_subst_var));
        needed_vars.push_back(decimal_part_of(real_subst_var));
        if (!int_subst_vars.contains(real_subst_var)) { //do not add int_version_of twice
            needed_vars.push_back(int_version_of(real_subst_var));
        }
    }
    return needed_vars;
}

}
