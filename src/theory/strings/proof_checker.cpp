/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Hans-Joerg Schurr, Aina Niemetz
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2024 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Implementation of strings proof checker.
 */

#include "theory/strings/proof_checker.h"

#include "expr/sequence.h"
#include "options/strings_options.h"
#include "theory/rewriter.h"
#include "theory/strings/core_solver.h"
#include "theory/strings/regexp_elim.h"
#include "theory/strings/regexp_entail.h"
#include "theory/strings/regexp_operation.h"
#include "theory/strings/term_registry.h"
#include "theory/strings/theory_strings_preprocess.h"
#include "theory/strings/theory_strings_utils.h"
#include "theory/strings/word.h"

using namespace cvc5::internal::kind;

namespace cvc5::internal {
namespace theory {
namespace strings {

StringProofRuleChecker::StringProofRuleChecker(NodeManager* nm,
                                               uint32_t alphaCard)
    : ProofRuleChecker(nm), d_alphaCard(alphaCard)
{
}

void StringProofRuleChecker::registerTo(ProofChecker* pc)
{
  pc->registerChecker(ProofRule::CONCAT_EQ, this);
  pc->registerChecker(ProofRule::CONCAT_UNIFY, this);
  pc->registerChecker(ProofRule::CONCAT_CONFLICT, this);
  pc->registerChecker(ProofRule::CONCAT_CONFLICT_DEQ, this);
  pc->registerChecker(ProofRule::CONCAT_SPLIT, this);
  pc->registerChecker(ProofRule::CONCAT_CSPLIT, this);
  pc->registerChecker(ProofRule::CONCAT_LPROP, this);
  pc->registerChecker(ProofRule::CONCAT_CPROP, this);
  pc->registerChecker(ProofRule::STRING_DECOMPOSE, this);
  pc->registerChecker(ProofRule::STRING_LENGTH_POS, this);
  pc->registerChecker(ProofRule::STRING_LENGTH_NON_EMPTY, this);
  pc->registerChecker(ProofRule::STRING_REDUCTION, this);
  pc->registerChecker(ProofRule::STRING_EAGER_REDUCTION, this);
  pc->registerChecker(ProofRule::RE_INTER, this);
  pc->registerChecker(ProofRule::RE_UNFOLD_POS, this);
  pc->registerChecker(ProofRule::RE_UNFOLD_NEG, this);
  pc->registerChecker(ProofRule::RE_UNFOLD_NEG_CONCAT_FIXED, this);
  pc->registerChecker(ProofRule::STRING_CODE_INJ, this);
  pc->registerChecker(ProofRule::STRING_SEQ_UNIT_INJ, this);
  pc->registerChecker(ProofRule::STRING_EXT, this);
  // trusted rule
  pc->registerTrustedChecker(ProofRule::MACRO_STRING_INFERENCE, this, 2);
}

Node StringProofRuleChecker::checkInternal(ProofRule id,
                                           const std::vector<Node>& children,
                                           const std::vector<Node>& args)
{
  NodeManager* nm = nodeManager();
  // core rules for word equations
  if (id == ProofRule::CONCAT_EQ || id == ProofRule::CONCAT_UNIFY
      || id == ProofRule::CONCAT_CONFLICT
      || id == ProofRule::CONCAT_CONFLICT_DEQ || id == ProofRule::CONCAT_SPLIT
      || id == ProofRule::CONCAT_CSPLIT || id == ProofRule::CONCAT_LPROP
      || id == ProofRule::CONCAT_CPROP)
  {
    Trace("strings-pfcheck") << "Checking id " << id << std::endl;
    Assert(children.size() >= 1);
    Assert(args.size() == 1);
    // all rules have an equality
    if (children[0].getKind() != Kind::EQUAL)
    {
      return Node::null();
    }
    // convert to concatenation form
    std::vector<Node> tvec;
    std::vector<Node> svec;
    utils::getConcat(children[0][0], tvec);
    utils::getConcat(children[0][1], svec);
    size_t nchildt = tvec.size();
    size_t nchilds = svec.size();
    TypeNode stringType = children[0][0].getType();
    // extract the Boolean corresponding to whether the rule is reversed
    bool isRev;
    if (!getBool(args[0], isRev))
    {
      return Node::null();
    }
    if (id == ProofRule::CONCAT_EQ)
    {
      Assert(children.size() == 1);
      size_t index = 0;
      std::vector<Node> tremVec;
      std::vector<Node> sremVec;
      // scan the concatenation until we exhaust child proofs
      while (index < nchilds && index < nchildt)
      {
        Node currT = tvec[isRev ? (nchildt - 1 - index) : index];
        Node currS = svec[isRev ? (nchilds - 1 - index) : index];
        if (currT != currS)
        {
          if (currT.isConst() && currS.isConst())
          {
            size_t sindex;
            // get the equal prefix/suffix, strip and add the remainders
            Node currR = Word::splitConstant(currT, currS, sindex, isRev);
            if (!currR.isNull())
            {
              // add the constant to remainder vec
              std::vector<Node>& rem = sindex == 0 ? tremVec : sremVec;
              rem.push_back(currR);
              // ignore the current component
              index++;
              // In other words, if we have (currS,currT) = ("ab","abc"), then
              // we proceed to the next component and add currR = "c" to
              // tremVec.
            }
            // otherwise if we are not the same prefix, then both will be added
            // Notice that we do not add maximal prefixes, in other words,
            // ("abc", "abd") may be added to the remainder vectors, and not
            // ("c", "d").
          }
          break;
        }
        index++;
      }
      Assert(index <= nchildt);
      Assert(index <= nchilds);
      // the remainders are equal
      tremVec.insert(isRev ? tremVec.begin() : tremVec.end(),
                     tvec.begin() + (isRev ? 0 : index),
                     tvec.begin() + nchildt - (isRev ? index : 0));
      sremVec.insert(isRev ? sremVec.begin() : sremVec.end(),
                     svec.begin() + (isRev ? 0 : index),
                     svec.begin() + nchilds - (isRev ? index : 0));
      // convert back to node
      Node trem = utils::mkConcat(tremVec, stringType);
      Node srem = utils::mkConcat(sremVec, stringType);
      return trem.eqNode(srem);
    }
    // all remaining rules do something with the first child of each side
    Node t0 = tvec[isRev ? nchildt - 1 : 0];
    Node s0 = svec[isRev ? nchilds - 1 : 0];
    if (id == ProofRule::CONCAT_UNIFY)
    {
      Assert(children.size() == 2);
      if (children[1].getKind() != Kind::EQUAL)
      {
        return Node::null();
      }
      for (size_t i = 0; i < 2; i++)
      {
        Node l = children[1][i];
        if (l.getKind() != Kind::STRING_LENGTH)
        {
          return Node::null();
        }
        Node term = i == 0 ? t0 : s0;
        if (l[0] == term)
        {
          continue;
        }
        // could be a spliced constant
        bool success = false;
        if (term.isConst() && l[0].isConst())
        {
          size_t lenL = Word::getLength(l[0]);
          success = (isRev && l[0] == Word::suffix(term, lenL))
                    || (!isRev && l[0] == Word::prefix(term, lenL));
        }
        if (!success)
        {
          return Node::null();
        }
      }
      return children[1][0][0].eqNode(children[1][1][0]);
    }
    else if (id == ProofRule::CONCAT_CONFLICT
             || id == ProofRule::CONCAT_CONFLICT_DEQ)
    {
      Assert(children.size() >= 1 && children.size() <= 2);
      if (!t0.isConst() || !s0.isConst())
      {
        // not constants
        return Node::null();
      }
      size_t sindex;
      Node r0 = Word::splitConstant(t0, s0, sindex, isRev);
      if (!r0.isNull())
      {
        // Not a conflict due to constants, i.e. s0 is a prefix of t0 or vice
        // versa.
        return Node::null();
      }
      // if a disequality was provided, ensure that it is correct
      if (id == ProofRule::CONCAT_CONFLICT_DEQ)
      {
        if (children.size() != 2 || children[1].getKind() != Kind::NOT
            || children[1][0].getKind() != Kind::EQUAL
            || children[1][0][0] != t0 || children[1][0][1] != s0)
        {
          return Node::null();
        }
      }
      else if (t0.getType().isSequence())
      {
        // we require the CONCAT_CONFLICT_DEQ for sequences
        return Node::null();
      }
      return nm->mkConst(false);
    }
    else if (id == ProofRule::CONCAT_SPLIT)
    {
      Assert(children.size() == 2);
      if (children[1].getKind() != Kind::NOT
          || children[1][0].getKind() != Kind::EQUAL
          || children[1][0][0].getKind() != Kind::STRING_LENGTH
          || children[1][0][0][0] != t0
          || children[1][0][1].getKind() != Kind::STRING_LENGTH
          || children[1][0][1][0] != s0)
      {
        return Node::null();
      }
    }
    else if (id == ProofRule::CONCAT_CSPLIT)
    {
      Assert(children.size() == 2);
      Node zero = nm->mkConstInt(Rational(0));
      Node one = nm->mkConstInt(Rational(1));
      if (children[1].getKind() != Kind::NOT
          || children[1][0].getKind() != Kind::EQUAL
          || children[1][0][0].getKind() != Kind::STRING_LENGTH
          || children[1][0][0][0] != t0 || children[1][0][1] != zero)
      {
        return Node::null();
      }
      if (!s0.isConst() || !s0.getType().isStringLike() || Word::isEmpty(s0))
      {
        return Node::null();
      }
    }
    else if (id == ProofRule::CONCAT_LPROP)
    {
      Assert(children.size() == 2);
      if (children[1].getKind() != Kind::GT
          || children[1][0].getKind() != Kind::STRING_LENGTH
          || children[1][0][0] != t0
          || children[1][1].getKind() != Kind::STRING_LENGTH
          || children[1][1][0] != s0)
      {
        return Node::null();
      }
    }
    else if (id == ProofRule::CONCAT_CPROP)
    {
      Assert(children.size() == 2);
      Node zero = nm->mkConstInt(Rational(0));

      Trace("pfcheck-strings-cprop")
          << "CONCAT_PROP, isRev=" << isRev << std::endl;
      if (children[1].getKind() != Kind::NOT
          || children[1][0].getKind() != Kind::EQUAL
          || children[1][0][0].getKind() != Kind::STRING_LENGTH
          || children[1][0][0][0] != t0 || children[1][0][1] != zero)
      {
        Trace("pfcheck-strings-cprop")
            << "...failed pattern match" << std::endl;
        return Node::null();
      }
      if (tvec.size() <= 1)
      {
        Trace("pfcheck-strings-cprop")
            << "...failed adjacent constant" << std::endl;
        return Node::null();
      }
      Node w1 = tvec[isRev ? nchildt - 2 : 1];
      if (!w1.isConst() || !w1.getType().isStringLike() || Word::isEmpty(w1))
      {
        Trace("pfcheck-strings-cprop")
            << "...failed adjacent constant content" << std::endl;
        return Node::null();
      }
      Node w2 = s0;
      if (!w2.isConst() || !w2.getType().isStringLike() || Word::isEmpty(w2))
      {
        Trace("pfcheck-strings-cprop") << "...failed constant" << std::endl;
        return Node::null();
      }
      // getConclusion expects the adjacent constant to be included
      t0 = nm->mkNode(Kind::STRING_CONCAT, isRev ? w1 : t0, isRev ? t0 : w1);
    }
    // use skolem cache
    SkolemCache skc(nm, nullptr);
    std::vector<Node> newSkolems;
    Node conc = CoreSolver::getConclusion(
        nodeManager(), t0, s0, id, isRev, &skc, newSkolems);
    return conc;
  }
  else if (id == ProofRule::STRING_DECOMPOSE)
  {
    Assert(children.size() == 1);
    Assert(args.size() == 1);
    bool isRev;
    if (!getBool(args[0], isRev))
    {
      return Node::null();
    }
    Node atom = children[0];
    if (atom.getKind() != Kind::GEQ || atom[0].getKind() != Kind::STRING_LENGTH)
    {
      return Node::null();
    }
    SkolemCache skc(nm, nullptr);
    std::vector<Node> newSkolems;
    Node conc = CoreSolver::getDecomposeConclusion(
        nodeManager(), atom[0][0], atom[1], isRev, &skc, newSkolems);
    return conc;
  }
  else if (id == ProofRule::STRING_REDUCTION
           || id == ProofRule::STRING_EAGER_REDUCTION
           || id == ProofRule::STRING_LENGTH_POS)
  {
    Assert(children.empty());
    Assert(args.size() >= 1);
    // These rules are based on calling a C++ method for returning a valid
    // lemma involving a single argument term.
    // Must convert to skolem form.
    Node t = args[0];
    Node ret;
    if (id == ProofRule::STRING_REDUCTION)
    {
      Assert(args.size() == 1);
      // we do not use optimizations
      SkolemCache skc(nm, nullptr);
      std::vector<Node> conj;
      ret = StringsPreprocess::reduce(t, conj, &skc, d_alphaCard);
      conj.push_back(t.eqNode(ret));
      ret = nm->mkAnd(conj);
    }
    else if (id == ProofRule::STRING_EAGER_REDUCTION)
    {
      Assert(args.size() == 1);
      SkolemCache skc(nm, nullptr);
      ret = TermRegistry::eagerReduce(t, &skc, d_alphaCard);
    }
    else if (id == ProofRule::STRING_LENGTH_POS)
    {
      Assert(args.size() == 1);
      ret = TermRegistry::lengthPositive(t);
    }
    if (ret.isNull())
    {
      return Node::null();
    }
    return ret;
  }
  else if (id == ProofRule::STRING_LENGTH_NON_EMPTY)
  {
    Assert(children.size() == 1);
    Assert(args.empty());
    Node nemp = children[0];
    if (nemp.getKind() != Kind::NOT || nemp[0].getKind() != Kind::EQUAL
        || !nemp[0][1].isConst() || !nemp[0][1].getType().isStringLike())
    {
      return Node::null();
    }
    if (!Word::isEmpty(nemp[0][1]))
    {
      return Node::null();
    }
    Node zero = nm->mkConstInt(Rational(0));
    Node clen = nm->mkNode(Kind::STRING_LENGTH, nemp[0][0]);
    return clen.eqNode(zero).notNode();
  }
  else if (id == ProofRule::RE_INTER)
  {
    Assert(children.size() >= 1);
    Assert(args.empty());
    std::vector<Node> reis;
    Node x;
    // make the regular expression intersection that summarizes all
    // memberships in the explanation
    for (const Node& c : children)
    {
      bool polarity = c.getKind() != Kind::NOT;
      Node catom = polarity ? c : c[0];
      if (catom.getKind() != Kind::STRING_IN_REGEXP)
      {
        return Node::null();
      }
      if (x.isNull())
      {
        x = catom[0];
      }
      else if (x != catom[0])
      {
        // different LHS
        return Node::null();
      }
      Node xcurr = catom[0];
      Node rcurr =
          polarity ? catom[1] : nm->mkNode(Kind::REGEXP_COMPLEMENT, catom[1]);
      reis.push_back(rcurr);
    }
    Node rei =
        reis.size() == 1 ? reis[0] : nm->mkNode(Kind::REGEXP_INTER, reis);
    return nm->mkNode(Kind::STRING_IN_REGEXP, x, rei);
  }
  else if (id == ProofRule::RE_UNFOLD_POS || id == ProofRule::RE_UNFOLD_NEG
           || id == ProofRule::RE_UNFOLD_NEG_CONCAT_FIXED)
  {
    Assert(children.size() == 1);
    Node skChild = children[0];
    if (id == ProofRule::RE_UNFOLD_NEG
        || id == ProofRule::RE_UNFOLD_NEG_CONCAT_FIXED)
    {
      if (skChild.getKind() != Kind::NOT
          || skChild[0].getKind() != Kind::STRING_IN_REGEXP)
      {
        Trace("strings-pfcheck") << "...fail, non-neg member" << std::endl;
        return Node::null();
      }
    }
    else if (skChild.getKind() != Kind::STRING_IN_REGEXP)
    {
      Trace("strings-pfcheck") << "...fail, non-pos member" << std::endl;
      return Node::null();
    }
    Node conc;
    if (id == ProofRule::RE_UNFOLD_POS)
    {
      Assert(args.empty());
      std::vector<Node> newSkolems;
      SkolemCache skc(nodeManager(), nullptr);
      conc =
          RegExpOpr::reduceRegExpPos(nodeManager(), skChild, &skc, newSkolems);
    }
    else if (id == ProofRule::RE_UNFOLD_NEG)
    {
      Assert(args.empty());
      conc = RegExpOpr::reduceRegExpNeg(nodeManager(), skChild);
    }
    else if (id == ProofRule::RE_UNFOLD_NEG_CONCAT_FIXED)
    {
      Assert(args.size() == 1);
      bool isRev;
      if (!getBool(args[0], isRev))
      {
        return Node::null();
      }
      Node r = skChild[0][1];
      if (r.getKind() != Kind::REGEXP_CONCAT)
      {
        Trace("strings-pfcheck") << "...fail, no concat regexp" << std::endl;
        return Node::null();
      }
      size_t index = isRev ? r.getNumChildren() - 1 : 0;
      Node reLen = RegExpEntail::getFixedLengthForRegexp(r[index]);
      if (reLen.isNull())
      {
        Trace("strings-pfcheck") << "...fail, non-fixed lengths" << std::endl;
        return Node::null();
      }
      conc = RegExpOpr::reduceRegExpNegConcatFixed(
          nodeManager(), skChild, reLen, isRev);
    }
    return conc;
  }
  else if (id == ProofRule::STRING_CODE_INJ)
  {
    Assert(children.empty());
    Assert(args.size() == 2);
    Assert(args[0].getType().isStringLike()
           && args[1].getType().isStringLike());
    Node c1 = nm->mkNode(Kind::STRING_TO_CODE, args[0]);
    Node c2 = nm->mkNode(Kind::STRING_TO_CODE, args[1]);
    Node eqNegOne = c1.eqNode(nm->mkConstInt(Rational(-1)));
    Node deq = c1.eqNode(c2).negate();
    Node eqn = args[0].eqNode(args[1]);
    return nm->mkNode(Kind::OR, eqNegOne, deq, eqn);
  }
  else if (id == ProofRule::STRING_SEQ_UNIT_INJ)
  {
    Assert(children.size() == 1);
    Assert(args.empty());
    if (children[0].getKind() != Kind::EQUAL)
    {
      return Node::null();
    }
    Node t[2];
    for (size_t i = 0; i < 2; i++)
    {
      Node c = children[0][i];
      Kind k = c.getKind();
      if (k == Kind::SEQ_UNIT || k == Kind::STRING_UNIT)
      {
        t[i] = c[0];
      }
      else if (c.isConst())
      {
        // notice that Word::getChars is not the right call here, since it
        // gets a vector of sequences of length one. We actually need to
        // extract the character.
        if (Word::getLength(c) == 1)
        {
          t[i] = Word::getNth(c, 0);
        }
      }
      if (t[i].isNull())
      {
        return Node::null();
      }
    }
    Trace("strings-pfcheck-debug")
        << "STRING_SEQ_UNIT_INJ: " << children[0] << " => " << t[0]
        << " == " << t[1] << std::endl;
    AlwaysAssert(t[0].getType() == t[1].getType());
    return t[0].eqNode(t[1]);
  }
  else if (id == ProofRule::STRING_EXT)
  {
    Assert(children.size() == 1);
    Assert(args.empty());
    Node deq = children[0];
    if (deq.getKind() != Kind::NOT || deq[0].getKind() != Kind::EQUAL
        || !deq[0][0].getType().isStringLike())
    {
      return Node::null();
    }
    SkolemCache skc(nm, nullptr);
    return CoreSolver::getExtensionalityConclusion(
        nm, deq[0][0], deq[0][1], &skc);
  }
  else if (id == ProofRule::MACRO_STRING_INFERENCE)
  {
    Assert(args.size() >= 3);
    return args[0];
  }
  return Node::null();
}

}  // namespace strings
}  // namespace theory
}  // namespace cvc5::internal
