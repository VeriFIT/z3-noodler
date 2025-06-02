#ifndef _NOODLER_NOODLIFICATION_H_
#define _NOODLER_NOODLIFICATION_H_

#include <memory>
#include <mata/nfa/strings.hh>

#include "formula.h"

namespace smt::noodler {
    struct TransducerNoodleElement {
        NFT transducer;
        std::shared_ptr<mata::nfa::Nfa> input_aut;
        unsigned input_index;
        std::shared_ptr<mata::nfa::Nfa> output_aut;
        unsigned output_index;

        TransducerNoodleElement(NFT transducer, std::shared_ptr<mata::nfa::Nfa> input_aut, unsigned input_index, std::shared_ptr<mata::nfa::Nfa> output_aut, unsigned output_index)
                    : transducer(transducer), input_aut(input_aut), input_index(input_index), output_aut(output_aut), output_index(output_index) { }
    };

    using TransducerNoodle = std::vector<TransducerNoodleElement>;

    std::vector<TransducerNoodle> noodlify_for_transducer(
        NFT nft,
        const std::vector<std::shared_ptr<mata::nfa::Nfa>>& input_automata,
        const std::vector<std::shared_ptr<mata::nfa::Nfa>>& output_automata,
        bool reduce_intersection = false
    );
}

#endif
