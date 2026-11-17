#ifndef _NOODLER_AXIOM_REPLAY_H_
#define _NOODLER_AXIOM_REPLAY_H_

#include <utility>
#include <vector>

#include "ast/ast.h"

namespace smt::noodler {

    /**
     * @brief Bookkeeping for replaying axioms deleted by backtracking.
     *
     * Z3 deletes the theory axioms added at a scope level when it backtracks below that level. Some terms are,
     * however, axiomatized only once (the theory remembers them as axiomatized and replaces them by the same fresh
     * variables forever). The axioms of such terms are recorded here together with the scope level at which they
     * were added. When the theory backtracks (pop()), the axioms added above the new level are moved to a queue of
     * pending axioms, which the theory adds again (take_pending()), so that Z3 and the theory agree on the
     * axiomatized terms.
     *
     * Only axioms valid on their own may be recorded (definitions of fresh variables or implications guarded by the
     * axiomatized term), since they are replayed regardless of the current assignment.
     */
    class AxiomReplay {
    public:
        /**
         * @brief While an instance of Recorder exists, the axioms passed to record() are recorded.
         */
        class Recorder {
        public:
            explicit Recorder(AxiomReplay& replay) : replay(replay) { ++replay.recording_depth; }
            ~Recorder() { --replay.recording_depth; }
            Recorder(const Recorder&) = delete;
            Recorder& operator=(const Recorder&) = delete;
        private:
            AxiomReplay& replay;
        };

        /**
         * @brief Are the added axioms to be recorded (i.e., does some Recorder exist)?
         */
        bool is_recording() const { return recording_depth > 0; }

        /**
         * @brief Record an axiom (a clause given by its literals as expressions) added at scope level @p level.
         * Does nothing if not recording. The levels of recorded axioms must be non-decreasing between pops
         * (which holds as the axioms are added at the current scope level).
         */
        void record(int level, const expr_ref_vector& clause) {
            if (!is_recording()) {
                return;
            }
            recorded.push_back({level, clause});
        }

        /**
         * @brief Backtracking to scope level @p new_level: the axioms recorded above it become pending.
         */
        void pop(int new_level) {
            while (!recorded.empty() && recorded.back().level > new_level) {
                pending.push_back(std::move(recorded.back().clause));
                recorded.pop_back();
            }
        }

        /**
         * @brief Are there axioms that need to be added again?
         */
        bool has_pending() const { return !pending.empty(); }

        /**
         * @brief Remove and return the axioms that need to be added again. They should be added at the current
         * level while recording (so that they are replayed again after the next backtracking).
         */
        std::vector<expr_ref_vector> take_pending() {
            std::vector<expr_ref_vector> res;
            std::swap(res, pending);
            return res;
        }

    private:
        struct RecordedAxiom {
            int level;
            expr_ref_vector clause;
        };

        std::vector<RecordedAxiom> recorded; // ordered by level (non-decreasing)
        std::vector<expr_ref_vector> pending;
        unsigned recording_depth = 0;
    };

} // namespace smt::noodler

#endif
