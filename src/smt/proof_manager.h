/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Haniel Barbosa, Abdalrhman Mohamed
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2024 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * The proof manager of SolverEngine.
 */

#include "cvc5_private.h"

#ifndef CVC5__SMT__PROOF_MANAGER_H
#define CVC5__SMT__PROOF_MANAGER_H

#include "context/cdhashmap.h"
#include "expr/node.h"
#include "options/proof_options.h"
#include "smt/env_obj.h"
#include "smt/proof_final_callback.h"

namespace cvc5::internal {

class ProofChecker;
class ProofNode;
class ProofNodeManager;
class ProofLogger;
class SolverEngine;

namespace rewriter {
class RewriteDb;
}

/** Modes for global Proof scopes introducing definitions and assertions. */
enum class ProofScopeMode
{
  /** No global scopes. Open proof. */
  NONE,
  /** Proof closed by a unified scope introducing definitions and assertions. */
  UNIFIED,
  /** Proof closed by 2 nested scopes introducing definitions and assertions. */
  DEFINITIONS_AND_ASSERTIONS,
};

namespace smt {

class Assertions;
class PreprocessProofGenerator;
class ProofPostprocess;

/**
 * This class is responsible for managing the proof output of SolverEngine, as
 * well as setting up the global proof checker and proof node manager.
 *
 * The proof production of an SolverEngine is directly impacted by whether, and
 * how, we are producing unsat cores:
 *
 * - If we are producing unsat cores using the old proof infrastructure, then
 *   SolverEngine will not have proofs in the sense of this proof manager.
 *
 * - If we are producing unsat cores using this proof infrastructure, then the
 *   SolverEngine will have proofs using this proof manager, according to the
 * unsat core mode:
 *
 *   - assumption mode: proofs only for preprocessing, not in sat solver or
 *   theory engine, and level of granularity set to off (unless otherwise
 *   specified by the user)
 *
 *   - sat-proof mode: proofs for preprocessing + sat solver, not in theory
 *   engine and level of granularity set to off (unless otherwise specified by
 *   the user)
 *
 *   - full-proof mode: proofs for the whole solver as normal
 *
 *   Note that if --produce-proofs is set then full-proof mode of unsat cores is
 *   forced.
 *
 * - If we are not producing unsat cores then the SolverEngine will have proofs
 * as long as --produce-proofs is on.
 *
 * - If SolverEngine has been configured in a way that is incompatible with
 * proofs then unsat core production will be disabled.
 */
class PfManager : protected EnvObj
{
 public:
  PfManager(Env& env);
  ~PfManager();
  /**
   * Print the proof on the given output stream in the given format.
   *
   * @param out The output stream.
   * @param fp The proof to print.
   * @param mode The format (e.g. cpc, alethe) to print.
   * @param scopeMode The expected form of fp (see ProofScopeMode).
   * @param assertionNames The named assertions of the input.
   */
  void printProof(std::ostream& out,
                  std::shared_ptr<ProofNode> fp,
                  options::ProofFormatMode mode,
                  ProofScopeMode scopeMode,
                  const std::map<Node, std::string>& assertionNames =
                      std::map<Node, std::string>());

  /**
   * Translate difficulty map. This takes a mapping dmap from preprocessed
   * assertions to values estimating their difficulty. It translates this
   * map so that dmap contains a mapping from *input* assertions to values
   * estimating their difficulty.
   *
   * It does this translation by constructing a proof of preprocessing for all
   * preprocessed assertions marked as having a difficulty, traversing those
   * proofs, and conditionally incrementing the difficulty of the input
   * assertion on which they depend. This is based on whether the free
   * assumption is the "source" of an assertion.
   *
   * @param dmap Map estimating the difficulty of preprocessed assertions
   * @param smt The SMT solver that owns the assertions and the preprocess
   * proof generator.
   */
  void translateDifficultyMap(std::map<Node, Node>& dmap, Assertions& as);

  /**
   * Connect proof to assertions
   *
   * Replaces the free assumptions of pfn that correspond to preprocessed
   * assertions maintained by smt with their corresponding proof of
   * preprocessing, which is obtained from the preprocessor of smt.
   *
   * Throws an assertion failure if pg cannot provide a closed proof with
   * respect to assertions in as. Note this includes equalities of the form
   * (= f (lambda (...) t)) which originate from define-fun commands for f.
   * These are considered assertions in the final proof.
   *
   * @param pfn The proof.
   * @param as Reference to the assertions.
   * @param scopeMode The expected form of fp (see ProofScopeMode).
   */
  std::shared_ptr<ProofNode> connectProofToAssertions(
      std::shared_ptr<ProofNode> pfn,
      Assertions& as,
      ProofScopeMode scopeMode = ProofScopeMode::UNIFIED);
  /**
   * Check proof. This call runs the final proof callback, which checks for
   * pedantic failures and takes statistics.
   * @param pfn The proof to check.
   */
  void checkFinalProof(std::shared_ptr<ProofNode> pfn);
  /**
   * Start proof logging. This is called when the SMT solver is initialized
   * and --proof-log is enabled.
   * @param out The output stream to log proofs on.
   * @param as Reference to the assertions.
   */
  void startProofLogging(std::ostream& out, Assertions& as);
  //--------------------------- access to utilities
  /** Get a pointer to the ProofChecker owned by this. */
  ProofChecker* getProofChecker() const;
  /** Get a pointer to the ProofNodeManager owned by this. */
  ProofNodeManager* getProofNodeManager() const;
  /** Get a pointer to the ProofLogger owned by this. */
  ProofLogger* getProofLogger() const;
  /** Get the rewrite database, containing definitions of rewrites from DSL. */
  rewriter::RewriteDb* getRewriteDatabase() const;
  /** Get the preprocess proof generator */
  PreprocessProofGenerator* getPreprocessProofGenerator() const;
  //--------------------------- end access to utilities
 private:
  /**
   * Get assertions from the assertions
   */
  void getAssertions(Assertions& as, std::vector<Node>& assertions);
  /**
   * Get definitions and assertions from the assertions
   */
  void getDefinitionsAndAssertions(Assertions& as,
                                   std::vector<Node>& definitions,
                                   std::vector<Node>& assertions);
  /** The false node */
  Node d_false;
  /** The rewrite proof database. */
  std::unique_ptr<rewriter::RewriteDb> d_rewriteDb;
  /** For the new proofs module */
  std::unique_ptr<ProofChecker> d_pchecker;
  /** A proof node manager based on the above checker */
  std::unique_ptr<ProofNodeManager> d_pnm;
  /** A proof logger, if proofLog is enabled */
  std::unique_ptr<ProofLogger> d_plog;
  /** The proof post-processor */
  std::unique_ptr<smt::ProofPostprocess> d_pfpp;
  /** The preprocess proof generator. */
  std::unique_ptr<PreprocessProofGenerator> d_pppg;
  /** The post process callback for finalization */
  ProofFinalCallback d_finalCb;
  /**
   * The finalizer, which is responsible for taking stats and checking for
   * (lazy) pedantic failures.
   */
  ProofNodeUpdater d_finalizer;
}; /* class SolverEngine */

}  // namespace smt
}  // namespace cvc5::internal

#endif /* CVC5__SMT__PROOF_MANAGER_H */
