/******************************************************************************
 * Top contributors (to current version):
 *
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2024 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Automata preprocessing pass.
 *
 */

#include "preprocessing/passes/automata.h"

#include <cmath>
#include <iterator>
#include <mata/nfa/nfa.hh>
#include <string>

#include "base/check.h"
#include "expr/node_algorithm.h"
#include "expr/skolem_manager.h"
#include "options/base_options.h"
#include "options/options.h"
#include "preprocessing/assertion_pipeline.h"
#include "preprocessing/preprocessing_pass_context.h"
#include "smt/logic_exception.h"
#include "util/rational.h"

inline int divide_by_two_and_floor(int k)
{
  return k % 2 == 0 ? k / 2 : (k < 0 ? k / 2 - 1 : k / 2);
}

using namespace cvc5::internal;
using namespace cvc5::internal::theory;
#define dbg(x) std::cout << #x << " = " << x << "\n"
namespace cvc5::internal {
namespace preprocessing {
namespace passes {

/* -------------------------------------------------------------------------- */

namespace {

}
/* -------------------------------------------------------------------------- */

typedef struct AtomicFormulaStructure
{
  kind::Kind_t formula_kind;
  std::vector<int> coefficients;
  std::vector<Node> vars;
  int c;
  unsigned int mod_value;
} AtomicFormulaStructure;

// I have to change this to fit amayas preprocessor output
AtomicFormulaStructure get_atomic_formula_structure(const TNode& node)
{
  TNode aux = node;
  int c = 0;
  unsigned int mod_value = 0;
  std::vector<Node> vars;
  std::vector<int> coefficients;

  switch (node.getKind())
  {
    // case a1x1 + ... anxn = c
    // RHS => Constantc c
    // LHS => Iterator over each AiXi if more than one variable, otherwise just
    // variable
    case kind::Kind_t::EQUAL:
    {
      TNode lhs = *aux.begin();
      // form x = c
      if (lhs.getKind() == kind::Kind_t::VARIABLE)
      {
        vars.push_back(lhs);
        coefficients.push_back(1);
      }
      // form ax = c
      else if (lhs.getKind() == kind::Kind_t::MULT)
      {
        int coef = stoi((*lhs.begin()).getConst<Rational>().toString());
        coefficients.push_back(coef);
        vars.push_back((*lhs.rbegin()));
      }
      // safely assume a1x1 + ... anxn = c
      else
      {
        for (const auto& val : lhs)
        {
          if (val.getKind() == kind::Kind_t::MULT)
          {
            vars.push_back(*val.rbegin());
            int coef = stoi((*val.begin()).getConst<Rational>().toString());
            coefficients.push_back(coef);
          }
          else
          {
            // for sure it's a single variable, so it's coefficient is 1
            vars.push_back(lhs);
            coefficients.push_back(1);
          }
        }
      }

      // getting c value in RHS
      const TNode rhs = *aux.rbegin();
      if (rhs.getKind() == kind::Kind_t::NEG)
      {
        c = -1 * stoi((*rhs.begin()).getConst<Rational>().toString());
      }
      else
      {
        c = stoi((rhs.getConst<Rational>().toString()));
      }
    }

    break;

      // case a1x1 + ... + anxn <= c
    case kind::Kind_t::LEQ:
    {
      TNode lhs = *aux.begin();
      // form x <= c
      if (lhs.getKind() == kind::Kind_t::VARIABLE)
      {
        vars.push_back(lhs);
        coefficients.push_back(1);
      }

      // form ax <= c
      else if (lhs.getKind() == kind::Kind_t::MULT)
      {
        int coef = stoi((*lhs.begin()).getConst<Rational>().toString());
        coefficients.push_back(coef);
        vars.push_back((*lhs.rbegin()));
      }
      // safely assume a1x1 + ... anxn = c
      else
      {
        for (const auto& val : lhs)
        {
          if (val.getKind() == kind::Kind_t::MULT)
          {
            vars.push_back(*val.rbegin());
            int coef = stoi((*val.begin()).getConst<Rational>().toString());
            coefficients.push_back(coef);
          }
          else
          {
            // for sure it's a single variable, so it's coefficient is 1
            vars.push_back(lhs);
            coefficients.push_back(1);
          }
        }
      }

      // getting c value in RHS
      const TNode rhs = *aux.rbegin();
      if (rhs.getKind() == kind::Kind_t::NEG)
      {
        c = -1 * stoi((*rhs.begin()).getConst<Rational>().toString());
      }
      else
      {
        c = stoi((rhs.getConst<Rational>().toString()));
      }
    }
    break;

    // CAN'T HANDLE MODULUS YET
    case kind::Kind_t::INTS_MODULUS_TOTAL:
    {
      TNode lhs = *aux.begin();   // the mod part
      TNode rhs = *aux.rbegin();  // c
      c = stoi(rhs.getConst<Rational>().toString());

      rhs = *lhs.rbegin();
      lhs = *lhs.begin();
      mod_value = stoi(rhs.getConst<Rational>().toString());
      for (const TNode& assertion : lhs)
      {
        if (assertion.getKind() == kind::Kind_t::MULT)
        {
          lhs = *assertion.begin();
          int64_t coef = stoi(lhs.getConst<Rational>().toString());
          coefficients.push_back(coef);
        }
        else if (assertion.getKind() == kind::Kind_t::VARIABLE)
        {
          coefficients.push_back(1);
        }
        else
        {
          std::cout << "We shouldn't get here" << std::endl;
        }
      }
      break;
    }
    default: break;
  }
  dbg("-------");
  std::cout << node << std::endl;
  for (int i = 0; i < (int)vars.size(); i++)
  {
    std::cout << coefficients[i] << " " << vars[i] << std::endl;
  }
  dbg(c);

  dbg("-------");
  return {node.getKind(), coefficients, vars, c, mod_value};
}

mata::nfa::Nfa Automata::build_nfa_for_formula(const Node& node)
{
  mata::nfa::Nfa formula_nfa;
  // std::cout << node << std::endl;
  // std::cout << node.getKind() << std::endl;
  switch (node.getKind())
  {
    case kind::Kind_t::EQUAL:
    case kind::Kind_t::LEQ:
    case kind::Kind_t::INTS_MODULUS_TOTAL:
    {
      formula_nfa = build_nfa_for_atomic_formula(node);
    }
    break;
    case kind::Kind_t::OR:
    {
      auto nfa1 = build_nfa_for_formula(*node.begin());
      auto nfa2 = build_nfa_for_formula(*node.rbegin());
      // And here a get the union
      nfa1.unite_nondet_with(nfa2);
      formula_nfa = nfa1;
    }
    break;
    case kind::Kind_t::AND:
    {
      auto nfa1 = build_nfa_for_formula(*node.begin());
      auto nfa2 = build_nfa_for_formula(*node.rbegin());
      formula_nfa = mata::nfa::intersection(nfa1, nfa2);
    }
    break;
    case kind::Kind_t::NOT:
    {
      auto nfa1 = build_nfa_for_formula(
          *node.begin());  // I AM ASSUMING THIS IS HOW TO DO IT WITH NOT,
                           // COULD BE SOMETHING ELSE
      nfa1.trim();
      // this could be wrong I should check it
      formula_nfa =
          nfa1.complement_deterministic(mata::utils::OrdVector<mata::Symbol>());
    }
    break;
    default: break;
  }
  return formula_nfa;
}

mata::nfa::Nfa Automata::build_nfa_for_atomic_formula(const Node& node)
{
  mata::nfa::Nfa aut;
  std::map<NfaState, unsigned int> nfa_state_to_int;
  auto [assertion_kind, coefficients, vars, c, mod_value] =
      get_atomic_formula_structure(node);
  unsigned int idx = 0;

  switch (assertion_kind)
  {
    case kind::Kind_t::EQUAL:
    {
      NfaState final_state = {0, 1};  // for this particular case we use the mod
                                      // value as a flag for the final state
      nfa_state_to_int[final_state] =
          idx++;  // final state is always gonna have index 0
      std::set<NfaState> states_to_process;

      aut.initial = {idx};
      nfa_state_to_int[{c, mod_value}] = idx++;
      states_to_process.insert({c, mod_value});

      while (!states_to_process.empty())
      {
        // this should remove the first element of the set
        NfaState state = *states_to_process.begin();
        states_to_process.erase(std::next(states_to_process.begin(), 0));

        // I only add the state to the automata if it is not the initial state
        // I already added
        unsigned long number_of_variables =
            static_cast<unsigned long>(vars_to_int.size());
        for (unsigned long sigma = 0; sigma < (1UL << number_of_variables);
             sigma++)
        {
          int new_c = state.c;

          int acc = 0;

          // this can be preocmputed
          for (int i = 0; i < (int)coefficients.size(); i++)
          {
            acc += coefficients.at(i)
                   * (sigma & (1 << vars_to_int[vars[i]]) ? 1 : 0);
          }
          new_c -= acc;
          if (new_c % 2 != 0)
          {
            continue;  // value is odd, we can continue
          }

          // if (state.c + acc == 0)
          // {
          //   aut.final.insert(nfa_state_to_int[{state.c, state.mod_value}]);
          // }
          new_c /= 2;

          if (nfa_state_to_int.count({new_c, state.mod_value}) == 0)
          {
            states_to_process.insert({new_c, state.mod_value});
            aut.add_state(idx);
            nfa_state_to_int[{new_c, state.mod_value}] = idx++;
          }
          aut.delta.add(nfa_state_to_int[{state.c, state.mod_value}],
                        sigma,
                        nfa_state_to_int[{new_c, state.mod_value}]);
          if (state.c + acc == 0)
          {
            aut.final.insert(nfa_state_to_int[final_state]);
            aut.delta.add(nfa_state_to_int[{state.c, state.mod_value}],
                          sigma,
                          nfa_state_to_int[final_state]);
          }
        }
      }
    }
    break;
    case kind::Kind_t::LEQ:
    {
      NfaState final_state = {0, 1};  // for this particular case we use the mod
                                      // value as a flag for the final state
      nfa_state_to_int[final_state] =
          idx++;  // final state is always gonna be index 0
      std::set<NfaState> states_to_process;

      aut.initial = {idx};
      nfa_state_to_int[{c, mod_value}] = idx++;
      states_to_process.insert({c, mod_value});
      while (!states_to_process.empty())
      {
        // this should remove the first element of the set
        NfaState state = *states_to_process.begin();
        states_to_process.erase(std::next(states_to_process.begin(), 0));

        // I only add the state to the automata if it is not the initial state
        // I already added
        unsigned long number_of_variables =
            static_cast<unsigned long>(vars_to_int.size());

        for (unsigned long sigma = 0; sigma < (1UL << number_of_variables);
             sigma++)
        {
          int new_c = state.c;

          int acc = 0;
          // this can be preocmputed

          for (int i = 0; i < (int)coefficients.size(); i++)
          {
            acc += coefficients.at(i)
                   * (sigma & (1 << vars_to_int[vars[i]]) ? 1 : 0);
          }
          new_c -= acc;
          new_c = divide_by_two_and_floor(new_c);

          if (nfa_state_to_int.count({new_c, state.mod_value}) == 0)
          {
            states_to_process.insert({new_c, state.mod_value});
            aut.add_state(idx);
            nfa_state_to_int[{new_c, state.mod_value}] = idx++;
          }
          aut.delta.add(nfa_state_to_int[{state.c, state.mod_value}],
                        sigma,
                        nfa_state_to_int[{new_c, state.mod_value}]);
          if (state.c + acc >= 0)
          {
            aut.final.insert(nfa_state_to_int[final_state]);
            aut.delta.add(nfa_state_to_int[{state.c, mod_value}],
                          sigma,
                          nfa_state_to_int[final_state]);
          }
        }
      }
    }
    break;
    default: break;
  }

  return aut;
}

Automata::Automata(PreprocessingPassContext* preprocContext)
    : PreprocessingPass(preprocContext, "automata")
{
}

PreprocessingPassResult Automata::applyInternal(
    AssertionPipeline* assertionsToPreprocess)
{
  std::cout << "Applying internal for automata preprocessing" << std::endl;
  AlwaysAssert(!options().base.incrementalSolving);

  /* collect all function applications and generate consistency lemmas
   * accordingly */
  std::vector<TNode> to_process;

  std::unordered_set<Node> vars;
  for (const Node& a : assertionsToPreprocess->ref())
  {
    expr::getVariables(a, vars);
    to_process.push_back(a);
  }

  // contains variables in formula and their indices for mapping
  unsigned int idx = 0;
  for (const Node& a : vars)
  {
    vars_to_int[a] = idx++;
  }

  // to_process.pop_back();  // only removing true formula

  int count = 0;
  for (const Node assertion : to_process)
  {
    // build automata for atomic formula
    mata::nfa::Nfa formula_automata = build_nfa_for_formula(assertion);
    if (count == 0)
    {
      global_nfa = formula_automata;
    }
    else
    {
      global_nfa = mata::nfa::intersection(global_nfa, formula_automata);
    }
    // join with general nfa called automata
    count++;
  }
  // global_nfa = mata::nfa::minimize(global_nfa);
  global_nfa.print_to_dot(std::cout);

  std::cout << (global_nfa.is_lang_empty() ? "automata says unsat"
                                           : "automata says sat")
            << std::endl;
  return PreprocessingPassResult::NO_CONFLICT;
}

}  // namespace passes
}  // namespace preprocessing
}  // namespace cvc5::internal
