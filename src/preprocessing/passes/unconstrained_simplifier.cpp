/******************************************************************************
 * Top contributors (to current version):
 *   Clark Barrett, Andres Noetzli, Aina Niemetz
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2024 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Simplifications based on unconstrained variables.
 *
 * This module implements a preprocessing phase which replaces certain
 * "unconstrained" expressions by variables.  Based on Roberto
 * Bruttomesso's PhD thesis.
 */

#include "preprocessing/passes/unconstrained_simplifier.h"

#include "expr/dtype.h"
#include "expr/skolem_manager.h"
#include "options/quantifiers_options.h"
#include "preprocessing/assertion_pipeline.h"
#include "preprocessing/preprocessing_pass_context.h"
#include "smt/logic_exception.h"
#include "theory/logic_info.h"
#include "theory/rewriter.h"
#include "util/bitvector.h"
#include "util/rational.h"
#include "util/statistics_registry.h"

using namespace std;
using namespace cvc5::internal::kind;
using namespace cvc5::internal::theory;

namespace cvc5::internal {
namespace preprocessing {
namespace passes {

UnconstrainedSimplifier::UnconstrainedSimplifier(
    PreprocessingPassContext* preprocContext)
    : PreprocessingPass(preprocContext, "unconstrained-simplifier"),
      d_numUnconstrainedElim(statisticsRegistry().registerInt(
          "preprocessor::number of unconstrained elims")),
      d_context(context()),
      d_substitutions(context())
{
}

struct unc_preprocess_stack_element
{
  TNode node;
  TNode parent;
  unc_preprocess_stack_element(TNode n) : node(n) {}
  unc_preprocess_stack_element(TNode n, TNode p) : node(n), parent(p) {}
}; /* struct unc_preprocess_stack_element */

void UnconstrainedSimplifier::visitAll(TNode assertion)
{
  // Do a topological sort of the subexpressions and substitute them
  vector<unc_preprocess_stack_element> toVisit;
  toVisit.push_back(assertion);

  while (!toVisit.empty())
  {
    // The current node we are processing
    TNode current = toVisit.back().node;
    TNode parent = toVisit.back().parent;
    toVisit.pop_back();

    TNodeCountMap::iterator find = d_visited.find(current);
    if (find != d_visited.end())
    {
      if (find->second == 1)
      {
        d_visitedOnce.erase(current);
        if (current.isVar())
        {
          d_unconstrained.erase(current);
        }
        else
        {
          // Also erase the children from the visited-once set when we visit a
          // node a second time, otherwise variables in this node are not
          // erased from the set of unconstrained variables.
          for (TNode childNode : current)
          {
            toVisit.push_back(unc_preprocess_stack_element(childNode, current));
          }
        }
      }
      ++find->second;
      continue;
    }

    d_visited[current] = 1;
    d_visitedOnce[current] = parent;

    if (current.getNumChildren() == 0)
    {
      if (current.isVar())
      {
        d_unconstrained.insert(current);
      }
    }
    else if (current.isClosure())
    {
      // Throw an exception. This should never happen in practice unless the
      // user specifically enabled unconstrained simplification in an illegal
      // logic.
      throw LogicException(
          "Cannot use unconstrained simplification in this logic, due to "
          "(possibly internally introduced) quantified formula.");
    }
    else
    {
      for (TNode childNode : current)
      {
        toVisit.push_back(unc_preprocess_stack_element(childNode, current));
      }
    }
  }
}

Node UnconstrainedSimplifier::newUnconstrainedVar(TypeNode t, TNode var)
{
  Node n = NodeManager::mkDummySkolem(
      "unconstrained",
      t,
      "a new var introduced because of unconstrained variable "
          + var.toString());
  return n;
}

void UnconstrainedSimplifier::processUnconstrained()
{
  NodeManager* nm = nodeManager();

  vector<TNode> workList(d_unconstrained.begin(), d_unconstrained.end());
  Node currentSub;
  TNode parent;
  bool swap;
  bool isSigned;
  bool strict;
  vector<TNode> delayQueueLeft;
  vector<Node> delayQueueRight;

  TNode current = workList.back();
  workList.pop_back();
  for (;;)
  {
    Assert(d_visitedOnce.find(current) != d_visitedOnce.end());
    parent = d_visitedOnce[current];
    if (!parent.isNull())
    {
      swap = isSigned = strict = false;
      bool checkParent = false;
      switch (parent.getKind())
      {
        // If-then-else operator - any two unconstrained children makes the
        // parent unconstrained
        case Kind::ITE:
        {
          Assert(parent[0] == current || parent[1] == current
                 || parent[2] == current);
          bool uCond =
              parent[0] == current
              || d_unconstrained.find(parent[0]) != d_unconstrained.end();
          bool uThen =
              parent[1] == current
              || d_unconstrained.find(parent[1]) != d_unconstrained.end();
          bool uElse =
              parent[2] == current
              || d_unconstrained.find(parent[2]) != d_unconstrained.end();
          if ((uCond && uThen) || (uCond && uElse) || (uThen && uElse))
          {
            if (d_unconstrained.find(parent) == d_unconstrained.end()
                && !d_substitutions.hasSubstitution(parent))
            {
              ++d_numUnconstrainedElim;
              if (uThen)
              {
                if (parent[1] != current)
                {
                  if (parent[1].isVar())
                  {
                    currentSub = parent[1];
                  }
                  else
                  {
                    Assert(d_substitutions.hasSubstitution(parent[1]));
                    currentSub = d_substitutions.apply(parent[1]);
                  }
                }
                else if (currentSub.isNull())
                {
                  currentSub = current;
                }
              }
              else if (parent[2] != current)
              {
                if (parent[2].isVar())
                {
                  currentSub = parent[2];
                }
                else
                {
                  Assert(d_substitutions.hasSubstitution(parent[2]));
                  currentSub = d_substitutions.apply(parent[2]);
                }
              }
              else if (currentSub.isNull())
              {
                currentSub = current;
              }
              current = parent;
            }
            else
            {
              currentSub = Node();
            }
          }
          else if (uCond)
          {
            Cardinality card = parent.getType().getCardinality();
            if (card.isFinite() && !card.isLargeFinite()
                && card.getFiniteCardinality() == 2)
            {
              // Special case: condition is unconstrained, then and else are
              // different, and total cardinality of the type is 2, then the
              // result is unconstrained
              Node test = rewrite(parent[1].eqNode(parent[2]));
              if (test == nm->mkConst<bool>(false))
              {
                ++d_numUnconstrainedElim;
                if (currentSub.isNull())
                {
                  currentSub = current;
                }
                currentSub = newUnconstrainedVar(parent.getType(), currentSub);
                current = parent;
              }
            }
          }
          break;
        }

        // Comparisons that return a different type - assuming domains are
        // larger than 1, any unconstrained child makes parent unconstrained as
        // well
        case Kind::EQUAL:
        {
          // equality uses strict type rule
          Assert(parent[0].getType() == parent[1].getType());
          CardinalityClass c = parent[0].getType().getCardinalityClass();
          if (c == CardinalityClass::ONE)
          {
            break;
          }
          // Otherwise if the cardinality class is INTERPRETED_ONE, then
          // the type may be one if finite model finding is enabled. We abort
          // in this case.
          if (c == CardinalityClass::INTERPRETED_ONE)
          {
            if (options().quantifiers.finiteModelFind)
            {
              break;
            }
          }
          if (parent[0].getType().isBoolean())
          {
            checkParent = true;
            break;
          }
          CVC5_FALLTHROUGH;
        }
        case Kind::BITVECTOR_COMP:
        case Kind::LT:
        case Kind::LEQ:
        case Kind::GT:
        case Kind::GEQ:
        {
          if (d_unconstrained.find(parent) == d_unconstrained.end()
              && !d_substitutions.hasSubstitution(parent))
          {
            ++d_numUnconstrainedElim;
            Assert(parent[0] != parent[1]
                   && (parent[0] == current || parent[1] == current));
            if (currentSub.isNull())
            {
              currentSub = current;
            }
            currentSub = newUnconstrainedVar(parent.getType(), currentSub);
            current = parent;
          }
          else
          {
            currentSub = Node();
          }
          break;
        }

        // Unary operators that propagate unconstrainedness
        case Kind::NOT:
        case Kind::BITVECTOR_NOT:
        case Kind::BITVECTOR_NEG:
        case Kind::NEG:
          ++d_numUnconstrainedElim;
          Assert(parent[0] == current);
          if (currentSub.isNull())
          {
            currentSub = current;
          }
          current = parent;
          break;

        // Unary operators that propagate unconstrainedness and return a
        // different type
        case Kind::BITVECTOR_EXTRACT:
          ++d_numUnconstrainedElim;
          Assert(parent[0] == current);
          if (currentSub.isNull())
          {
            currentSub = current;
          }
          currentSub = newUnconstrainedVar(parent.getType(), currentSub);
          current = parent;
          break;

        // Operators returning same type requiring all children to be
        // unconstrained
        case Kind::AND:
        case Kind::OR:
        case Kind::IMPLIES:
        case Kind::BITVECTOR_AND:
        case Kind::BITVECTOR_OR:
        case Kind::BITVECTOR_NAND:
        case Kind::BITVECTOR_NOR:
        {
          bool allUnconstrained = true;
          for (TNode child : parent)
          {
            if (d_unconstrained.find(child) == d_unconstrained.end())
            {
              allUnconstrained = false;
              break;
            }
          }
          if (allUnconstrained)
          {
            checkParent = true;
          }
        }
        break;

        // Require all children to be unconstrained and different
        case Kind::BITVECTOR_SHL:
        case Kind::BITVECTOR_LSHR:
        case Kind::BITVECTOR_ASHR:
        case Kind::BITVECTOR_UDIV:
        case Kind::BITVECTOR_UREM:
        case Kind::BITVECTOR_SDIV:
        case Kind::BITVECTOR_SREM:
        case Kind::BITVECTOR_SMOD:
        {
          bool allUnconstrained = true;
          bool allDifferent = true;
          for (TNode::iterator child_it = parent.begin();
               child_it != parent.end();
               ++child_it)
          {
            if (d_unconstrained.find(*child_it) == d_unconstrained.end())
            {
              allUnconstrained = false;
              break;
            }
            for (TNode::iterator child_it2 = child_it + 1;
                 child_it2 != parent.end();
                 ++child_it2)
            {
              if (*child_it == *child_it2)
              {
                allDifferent = false;
                break;
              }
            }
          }
          if (allUnconstrained && allDifferent)
          {
            checkParent = true;
          }
          break;
        }

        // Requires all children to be unconstrained and different, and returns
        // a different type
        case Kind::BITVECTOR_CONCAT:
        {
          bool allUnconstrained = true;
          bool allDifferent = true;
          for (TNode::iterator child_it = parent.begin();
               child_it != parent.end();
               ++child_it)
          {
            if (d_unconstrained.find(*child_it) == d_unconstrained.end())
            {
              allUnconstrained = false;
              break;
            }
            for (TNode::iterator child_it2 = child_it + 1;
                 child_it2 != parent.end();
                 ++child_it2)
            {
              if (*child_it == *child_it2)
              {
                allDifferent = false;
                break;
              }
            }
          }
          if (allUnconstrained && allDifferent)
          {
            if (d_unconstrained.find(parent) == d_unconstrained.end()
                && !d_substitutions.hasSubstitution(parent))
            {
              ++d_numUnconstrainedElim;
              if (currentSub.isNull())
              {
                currentSub = current;
              }
              currentSub = newUnconstrainedVar(parent.getType(), currentSub);
              current = parent;
            }
            else
            {
              currentSub = Node();
            }
          }
        }
        break;

        // N-ary operators returning same type requiring at least one child to
        // be unconstrained
        case Kind::ADD:
        case Kind::SUB:
          if (current.getType().isInteger() && !parent.getType().isInteger())
          {
            break;
          }
          CVC5_FALLTHROUGH;
        case Kind::XOR:
        case Kind::BITVECTOR_XOR:
        case Kind::BITVECTOR_XNOR:
        case Kind::BITVECTOR_ADD:
        case Kind::BITVECTOR_SUB: checkParent = true; break;

        // Multiplication/division: must be non-integer and other operand must
        // be non-zero
        case Kind::MULT:
        case Kind::DIVISION:
        {
          Assert(parent.getNumChildren() == 2);
          TNode other;
          if (parent[0] == current)
          {
            other = parent[1];
          }
          else
          {
            Assert(parent[1] == current);
            other = parent[0];
          }
          if (d_unconstrained.find(other) != d_unconstrained.end())
          {
            if (d_unconstrained.find(parent) == d_unconstrained.end()
                && !d_substitutions.hasSubstitution(parent))
            {
              if (current.getType().isInteger() && other.getType().isInteger())
              {
                Assert(parent.getKind() == Kind::DIVISION
                       || parent.getType().isInteger());
                if (parent.getKind() == Kind::DIVISION)
                {
                  break;
                }
              }
              ++d_numUnconstrainedElim;
              if (currentSub.isNull())
              {
                currentSub = current;
              }
              current = parent;
            }
            else
            {
              currentSub = Node();
            }
          }
          else
          {
            // if only the denominator of a division is unconstrained, can't
            // set it to 0 so the result is not unconstrained
            if (parent.getKind() == Kind::DIVISION && current == parent[1])
            {
              break;
            }
            // if we are an integer, the only way we are unconstrained is if
            // we are a MULT by -1
            if (current.getType().isInteger())
            {
              // div/mult by 1 should have been simplified
              Assert(other != nm->mkConstInt(Rational(1)));
              // div by -1 should have been simplified
              if (other != nm->mkConstInt(Rational(-1)))
              {
                break;
              }
              else
              {
                Assert(parent.getKind() == Kind::MULT);
                Assert(parent.getType().isInteger());
              }
            }
            else
            {
              // TODO(#2377): could build ITE here
              Node test = other.eqNode(
                  nm->mkConstRealOrInt(other.getType(), Rational(0)));
              if (rewrite(test) != nm->mkConst<bool>(false))
              {
                break;
              }
            }
            ++d_numUnconstrainedElim;
            if (currentSub.isNull())
            {
              currentSub = current;
            }
            current = parent;
          }
          break;
        }

        // Bitvector MULT - current must only appear once in the children:
        // all other children must be unconstrained or odd
        case Kind::BITVECTOR_MULT:
        {
          bool found = false;
          bool done = false;

          for (TNode child : parent)
          {
            if (child == current)
            {
              if (found)
              {
                done = true;
                break;
              }
              found = true;
              continue;
            }
            else if (d_unconstrained.find(child) == d_unconstrained.end())
            {
              Node extractOp =
                  nm->mkConst<BitVectorExtract>(BitVectorExtract(0, 0));
              vector<Node> children;
              children.push_back(child);
              Node test = nm->mkNode(extractOp, children);
              BitVector one(1, unsigned(1));
              test = test.eqNode(nm->mkConst<BitVector>(one));
              if (rewrite(test) != nm->mkConst<bool>(true))
              {
                done = true;
                break;
              }
            }
          }
          if (done)
          {
            break;
          }
          checkParent = true;
          break;
        }

        // Uninterpreted function - if domain is infinite, no quantifiers are
        // used, and any child is unconstrained, result is unconstrained
        case Kind::APPLY_UF:
          if (logicInfo().isQuantified()
              || !current.getType().getCardinality().isInfinite())
          {
            break;
          }
          if (d_unconstrained.find(parent) == d_unconstrained.end()
              && !d_substitutions.hasSubstitution(parent))
          {
            ++d_numUnconstrainedElim;
            if (currentSub.isNull())
            {
              currentSub = current;
            }
            // always introduce a new variable; it is unsound to try to reuse
            // currentSub as the variable, see issue #4469.
            currentSub = newUnconstrainedVar(parent.getType(), currentSub);
            current = parent;
          }
          else
          {
            currentSub = Node();
          }
          break;

        // Array select - if array is unconstrained, so is result
        case Kind::SELECT:
          if (parent[0] == current)
          {
            ++d_numUnconstrainedElim;
            Assert(current.getType().isArray());
            if (currentSub.isNull())
            {
              currentSub = current;
            }
            currentSub = newUnconstrainedVar(
                current.getType().getArrayConstituentType(), currentSub);
            current = parent;
          }
          break;

        // Array store - if both store and value are unconstrained, so is
        // resulting store
        case Kind::STORE:
          if (((parent[0] == current
                && d_unconstrained.find(parent[2]) != d_unconstrained.end())
               || (parent[2] == current
                   && d_unconstrained.find(parent[0])
                          != d_unconstrained.end())))
          {
            if (d_unconstrained.find(parent) == d_unconstrained.end()
                && !d_substitutions.hasSubstitution(parent))
            {
              ++d_numUnconstrainedElim;
              if (parent[0] != current)
              {
                if (parent[0].isVar())
                {
                  currentSub = parent[0];
                }
                else
                {
                  Assert(d_substitutions.hasSubstitution(parent[0]));
                  currentSub = d_substitutions.apply(parent[0]);
                }
              }
              else if (currentSub.isNull())
              {
                currentSub = current;
              }
              current = parent;
            }
            else
            {
              currentSub = Node();
            }
          }
          break;

        // Bit-vector comparisons: replace with new Boolean variable, but have
        // to also conjoin with a side condition as there is always one case
        // when the comparison is forced to be false
        case Kind::BITVECTOR_ULT:
        case Kind::BITVECTOR_UGE:
        case Kind::BITVECTOR_UGT:
        case Kind::BITVECTOR_ULE:
        case Kind::BITVECTOR_SLT:
        case Kind::BITVECTOR_SGE:
        case Kind::BITVECTOR_SGT:
        case Kind::BITVECTOR_SLE:
        {
          // Tuples over (signed, swap, strict).
          switch (parent.getKind())
          {
            case Kind::BITVECTOR_UGE: break;
            case Kind::BITVECTOR_ULT: strict = true; break;
            case Kind::BITVECTOR_ULE: swap = true; break;
            case Kind::BITVECTOR_UGT:
              swap = true;
              strict = true;
              break;
            case Kind::BITVECTOR_SGE: isSigned = true; break;
            case Kind::BITVECTOR_SLT:
              isSigned = true;
              strict = true;
              break;
            case Kind::BITVECTOR_SLE:
              isSigned = true;
              swap = true;
              break;
            case Kind::BITVECTOR_SGT:
              isSigned = true;
              swap = true;
              strict = true;
              break;
            default: Unreachable();
          }
          TNode other;
          bool left = false;
          if (parent[0] == current)
          {
            other = parent[1];
            left = true;
          }
          else
          {
            Assert(parent[1] == current);
            other = parent[0];
          }
          if (d_unconstrained.find(other) != d_unconstrained.end())
          {
            if (d_unconstrained.find(parent) == d_unconstrained.end()
                && !d_substitutions.hasSubstitution(parent))
            {
              ++d_numUnconstrainedElim;
              if (currentSub.isNull())
              {
                currentSub = current;
              }
              currentSub = newUnconstrainedVar(parent.getType(), currentSub);
              current = parent;
            }
            else
            {
              currentSub = Node();
            }
          }
          else
          {
            unsigned size = current.getType().getBitVectorSize();
            BitVector bv =
                isSigned ? BitVector(size, Integer(1).multiplyByPow2(size - 1))
                         : BitVector(size, unsigned(0));
            if (swap == left)
            {
              bv = ~bv;
            }
            if (currentSub.isNull())
            {
              currentSub = current;
            }
            currentSub = newUnconstrainedVar(parent.getType(), currentSub);
            current = parent;
            Node test = rewrite(other.eqNode(nm->mkConst<BitVector>(bv)));
            if (test == nm->mkConst<bool>(false))
            {
              break;
            }
            currentSub = strict ? currentSub.andNode(test.notNode())
                                : currentSub.orNode(test);
            // Delay adding this substitution - see comment at end of function
            delayQueueLeft.push_back(current);
            delayQueueRight.push_back(currentSub);
            currentSub = Node();
            parent = TNode();
          }
          break;
        }

        // Do nothing
        case Kind::BITVECTOR_SIGN_EXTEND:
        case Kind::BITVECTOR_ZERO_EXTEND:
        case Kind::BITVECTOR_REPEAT:
        case Kind::BITVECTOR_ROTATE_LEFT:
        case Kind::BITVECTOR_ROTATE_RIGHT:

        default: break;
      }
      if (checkParent)
      {
        // run for various cases from above
        if (d_unconstrained.find(parent) == d_unconstrained.end()
            && !d_substitutions.hasSubstitution(parent))
        {
          ++d_numUnconstrainedElim;
          if (currentSub.isNull())
          {
            currentSub = current;
          }
          current = parent;
        }
        else
        {
          currentSub = Node();
        }
      }
      if (current == parent && d_visited[parent] == 1)
      {
        d_unconstrained.insert(parent);
        continue;
      }
    }
    if (!currentSub.isNull())
    {
      Trace("unc-simp")
          << "UnconstrainedSimplifier::processUnconstrained: introduce "
          << currentSub << " for " << current << ", parent " << parent
          << std::endl;
      Assert(currentSub.isVar());
      d_substitutions.addSubstitution(current, currentSub, false);
    }
    if (workList.empty())
    {
      break;
    }
    current = workList.back();
    currentSub = Node();
    workList.pop_back();
  }
  TNode left;
  Node right;
  // All substitutions except those arising from bitvector comparisons are
  // substitutions t -> x where x is a variable.  This allows us to build the
  // substitution very quickly (never invalidating the substitution cache).
  // Bitvector comparisons are more complicated and may require
  // back-substitution and cache-invalidation.  So we do these last.
  while (!delayQueueLeft.empty())
  {
    left = delayQueueLeft.back();
    if (!d_substitutions.hasSubstitution(left))
    {
      right = d_substitutions.apply(delayQueueRight.back());
      d_substitutions.addSubstitution(delayQueueLeft.back(), right);
    }
    delayQueueLeft.pop_back();
    delayQueueRight.pop_back();
  }
}

PreprocessingPassResult UnconstrainedSimplifier::applyInternal(
    AssertionPipeline* assertionsToPreprocess)
{
  d_preprocContext->spendResource(Resource::PreprocessStep);

  const std::vector<Node>& assertions = assertionsToPreprocess->ref();

  d_context->push();

  for (const Node& assertion : assertions)
  {
    visitAll(assertion);
  }

  if (!d_unconstrained.empty())
  {
    processUnconstrained();
    for (size_t i = 0, asize = assertions.size(); i < asize; ++i)
    {
      Node a = assertions[i];
      Node as = d_substitutions.apply(a);
      // nothing to do if substitutions has no effect, skip
      if (as != a)
      {
        // replace the assertion
        assertionsToPreprocess->replace(
            i, as, nullptr, TrustId::PREPROCESS_UNCONSTRAINED_SIMP);
        assertionsToPreprocess->ensureRewritten(i);
      }
    }
  }

  // to clear substitutions map
  d_context->pop();

  d_visited.clear();
  d_visitedOnce.clear();
  d_unconstrained.clear();

  return PreprocessingPassResult::NO_CONFLICT;
}


}  // namespace passes
}  // namespace preprocessing
}  // namespace cvc5::internal
