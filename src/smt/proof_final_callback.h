/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Hans-Joerg Schurr, Abdalrhman Mohamed
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2025 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * The module for final processing proof nodes.
 */

#include "cvc5_private.h"

#ifndef CVC5__SMT__PROOF_FINAL_CALLBACK_H
#define CVC5__SMT__PROOF_FINAL_CALLBACK_H

#include <map>
#include <sstream>
#include <unordered_set>

#include "proof/proof_node_updater.h"
#include "proof/trust_id.h"
#include "rewriter/rewrites.h"
#include "smt/env_obj.h"
#include "theory/inference_id.h"
#include "util/statistics_stats.h"
#include "theory/theory_id.h"

namespace cvc5::internal {
namespace smt {

/** Final callback class, for stats and pedantic checking */
class ProofFinalCallback : protected EnvObj, public ProofNodeUpdaterCallback
{
 public:
  ProofFinalCallback(Env& env);
  /**
   * Initialize, called once for each new ProofNode to process. This initializes
   * static information to be used by successive calls to update.
   */
  void initializeUpdate();
  /** Finalize the proof node, which checks assertions and adds to stats. */
  void finalize(std::shared_ptr<ProofNode> pn) override;
  /** was pedantic failure */
  bool wasPedanticFailure(std::ostream& out) const;

 private:
  /** Counts number of postprocessed proof nodes for each kind of proof rule */
  HistogramStat<ProofRule> d_ruleCount;
  /**
   * Counts number of proof nodes for each kind of proof rule that cannot be
   * printed in CPC+Eunoia.
   */
  HistogramStat<ProofRule> d_ruleEouCount;
  /**
   * Counts number of postprocessed proof nodes of rule INSTANTIATE that were
   * marked with the given inference id.
   */
  HistogramStat<theory::InferenceId> d_instRuleIds;
  /**
   * Counts number of postprocessed proof nodes for each kind of DSL proof rule
   */
  HistogramStat<ProofRewriteRule> d_dslRuleCount;
  /**
   * Counts number of postprocessed proof nodes for each kind of THEORY_REWRITE
   */
  HistogramStat<ProofRewriteRule> d_theoryRewriteRuleCount;
  /**
   * Counts number of proof nodes for each kind of THEORY_REWRITE that cannot be
   * printed in CPC+Eunoia.
   */
  HistogramStat<ProofRewriteRule> d_theoryRewriteEouCount;
  /**
   * Counts number of postprocessed proof nodes for each trusted step
   */
  HistogramStat<TrustId> d_trustIds;
  /**
   * Counts number of theory ids in TRUST_THEORY_REWRITE steps.
   */
  HistogramStat<theory::TheoryId> d_trustTheoryRewriteCount;
  /**
   * Counts number of theory ids in TRUST / THEORY_LEMMA steps.
   */
  HistogramStat<theory::TheoryId> d_trustTheoryLemmaCount;
  /** Total number of postprocessed rule applications */
  IntStat d_totalRuleCount;
  /** The minimum pedantic level of any rule encountered */
  IntStat d_minPedanticLevel;
  /** The total number of final proofs */
  IntStat d_numFinalProofs;
  /** Was there a pedantic failure? */
  bool d_pedanticFailure;
  /**
   * Should we check for proof holes? True if statistics are enabled or if
   * check-proofs-complete is true.
   */
  bool d_checkProofHoles;
  /** The pedantic failure string for debugging */
  std::stringstream d_pedanticFailureOut;
};

}  // namespace smt
}  // namespace cvc5::internal

#endif
