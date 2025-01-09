
/******************************************************************************
 * Top contributors (to current version):
 *  Luís Felipe Ramos Ferreira, Haniel Barbosa
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2024 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Applies the preprocessing of a LIA formula into a automata problem and
 * calls a external automata solver. Algebraic Reasoning Meets Automata in
Solving Linear Integer Arithmetic
 *
 *
 * Calls Theory::preprocess(...) on every assertion of the formula.
 */

#include <mata/nfa/nfa.hh>

#include "cvc5_private.h"

#ifndef CVC5__PREPROCESSING__PASSES__AUTOMATA_H
#define CVC5__PREPROCESSING__PASSES__AUTOMATA_H

#include "preprocessing/preprocessing_pass.h"

namespace cvc5::internal {
namespace preprocessing {
namespace passes {

typedef struct NfaState
{
  int c;
  unsigned int mod_value;  // should be 0 when it is not a mod expression

  bool operator<(const NfaState& other) const
  {
    if (c != other.c) return c < other.c;
    return mod_value < other.mod_value;
  }
} NfaState;

class Automata : public PreprocessingPass
{
 public:
  Automata(PreprocessingPassContext* preprocContext);

 protected:
  PreprocessingPassResult applyInternal(
      AssertionPipeline* assertionsToPreprocess) override;
  mata::nfa::Nfa build_nfa_for_atomic_formula(const Node& node);
  mata::nfa::Nfa build_nfa_for_formula(const Node& node);
  std::map<Node, int> get_posible_solution();

 private:
  mata::nfa::Nfa global_nfa;
  std::unordered_map<Node, unsigned int> vars_to_int;
};

}  // namespace passes
}  // namespace preprocessing
}  // namespace cvc5::internal

#endif /* CVC5__PREPROCESSING__PASSES__AUTOMATA_H */
