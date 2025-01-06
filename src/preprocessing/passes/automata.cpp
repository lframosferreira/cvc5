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

int divide_by_two_and_floor(int k)
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

// void buildDfa(const int& initial_state,
//               const std::vector<int> coefficients,
//               std::map<int, std::vector<AutomataEdge>>& dfa,
//               const kind::Kind_t& assertion_kind,
//               int mod_value)
// {
//   int number_of_coefficients = static_cast<int>(coefficients.size());
//   for (const auto& e : coefficients)
//   {
//     std::cout << e << " ";
//   }
//   std::cout << std::endl;
//
//   std::queue<int> states_to_process;
//   states_to_process.push(initial_state);
//   std::set<int> processed_states;
//
//   // I am assuming number of coefficients at most 64, this is obviously not
//   // the general case
//   while (!states_to_process.empty())
//   {
//     int c = states_to_process.front();
//     states_to_process.pop();
//     if (processed_states.find(c) != processed_states.end())
//     {
//       // don't need to process it again
//       continue;
//     }
//     processed_states.insert(c);
//     dfa.insert({c, {}});
//     for (int transition = 0; transition < (1 << number_of_coefficients);
//          transition++)
//     {
//       int k = c;
//       // computing k
//
//       int transition_acc_sentinel = c;
//       for (int i = 0; i < number_of_coefficients; i++)
//       {
//         bool condition = (1 << i) & transition;
//         if (condition)
//         {
//           k -= coefficients.at(i);
//           transition_acc_sentinel += coefficients.at(i);
//         }
//       }
//       switch (assertion_kind)
//       {
//         case kind::Kind_t::EQUAL:
//         {
//           if (k % 2 == 0)
//           {
//             bool is_transition_acc = transition_acc_sentinel == 0;
//             struct AutomataEdge edge = {k / 2, transition,
//             is_transition_acc}; dfa.at(c).push_back(edge);
//             states_to_process.push(k / 2);
//           }
//
//           break;
//         }
//         case kind::Kind_t::LEQ:
//         {
//           bool is_transition_acc = transition_acc_sentinel >= 0;
//           int new_state = k % 2 == 0 ? k / 2 : (k < 0 ? k / 2 - 1 : k / 2);
//           std::cout << "--------" << std::endl;
//           std::cout << k << std::endl;
//           std::cout << new_state << std::endl;
//           std::cout << "--------" << std::endl;
//           struct AutomataEdge edge = {new_state, transition,
//           is_transition_acc}; dfa.at(c).push_back(edge);
//           states_to_process.push(new_state);
//           break;
//         };
//         case kind::Kind_t::INTS_MODULUS_TOTAL:
//         {
//           if (mod_value % 2 == 0)
//           {
//             if (k % 2 == 0)
//             {
//               bool is_transition_acc = transition_acc_sentinel % mod_value ==
//               0; int new_state = (mod_value + ((k / 2) % mod_value)) %
//               mod_value; struct AutomataEdge edge = {
//                   new_state, transition, is_transition_acc};
//               dfa.at(c).push_back(edge);
//               states_to_process.push(new_state);
//             }
//           }
//           else
//           {
//           }
//
//           break;
//         }
//         default:
//         {
//           std::cout << "Not LIA" << std::endl;
//           break;
//         }
//       }
//     }
//   }
// }

// to_process.pop_back();  // removing redundant TRUE constant
//
// // after preprocessing, we always have exp = c + SUMexp

typedef struct AtomicFormulaStructure
{
  kind::Kind_t formula_kind;
  std::vector<int> coefficients;
  std::vector<Node> vars;
  int c;
  unsigned int mod_value;
} AtomicFormulaStructure;

AtomicFormulaStructure get_atomic_formula_structure(const TNode& a)
{
  TNode aux = a;
  int c = 0;
  unsigned int mod_value = 0;
  std::vector<Node> vars;
  std::vector<int> coefficients;
  kind::Kind_t assertion_kind = kind::Kind_t::EQUAL;

  switch (aux.getKind())
  {
    case kind::Kind_t::EQUAL:
    {
      if ((*aux.begin()).getKind() == kind::Kind_t::INTS_MODULUS_TOTAL)
      {
        assertion_kind = kind::Kind_t::INTS_MODULUS_TOTAL;
      }
      else
      {
        assertion_kind = kind::Kind_t::EQUAL;
      }
      break;
    }
    case kind::Kind_t::NOT:
    {
      assertion_kind = kind::Kind_t::LEQ;
      break;
    }
    default: break;
  }

  // preprocessing to get coefficients of every formula. Each kind has a
  // different format in cvc5 after preprocessing
  switch (assertion_kind)
  {
    // case a1x1 + ... anxn = c
    case kind::Kind_t::EQUAL:
    {
      TNode lhs = *aux.begin();
      if (lhs.getKind() == kind::Kind_t::MULT)
      {
        vars.push_back(*lhs.rbegin());
        lhs = *lhs.begin();
        int64_t coef = stoi(lhs.getConst<Rational>().toString());
        coefficients.push_back(coef);
      }
      else
      {
        // for sure it's a single var
        vars.push_back(lhs);
        coefficients.push_back(1);
      }

      // now process right side of relation
      TNode rhs = *aux.rbegin();
      if (rhs.getKind() == kind::Kind_t::CONST_INTEGER)
      {
        c = stoi(rhs.getConst<Rational>().toString());
      }
      else
      {
        for (const TNode& assertion : rhs)
        {
          if (assertion.getKind() == kind::Kind_t::MULT)
          {
            lhs = *assertion.begin();
            int64_t coef = stoi(lhs.getConst<Rational>().toString());
            coefficients.push_back(-1 * coef);
            vars.push_back(*assertion.rbegin());
          }
          else if (assertion.getKind() == kind::Kind_t::VARIABLE)
          {
            coefficients.push_back(-1);
            vars.push_back(assertion);
          }
          else
          {
            // for sure it's the constant C
            c = stoi(assertion.getConst<Rational>().toString());
          }
        }
      }
      break;
    }

      // case a1x1 + ... + anxn <= c (cvc5 converts into a not (>=))
    case kind::Kind_t::LEQ:
    {
      aux = *aux.begin();
      TNode lhs = *aux.begin();
      TNode rhs = *(aux.rbegin());
      c = stoi(rhs.getConst<Rational>().toString());
      c--;
      if (lhs.getKind() == kind::Kind_t::VARIABLE)
      {
        coefficients.push_back(1);
        vars.push_back(lhs);
      }
      else
      {
        for (const TNode& assertion : lhs)
        {
          if (assertion.getKind() == kind::Kind_t::MULT)
          {
            lhs = *assertion.begin();
            int64_t coef = stoi(lhs.getConst<Rational>().toString());
            coefficients.push_back(coef);
            vars.push_back(*assertion.rbegin());
          }
          else if (assertion.getKind() == kind::Kind_t::VARIABLE)
          {
            coefficients.push_back(1);
            vars.push_back(assertion);
          }
          else
          {
            std::cout << "We shouldn't get here" << std::endl;
          }
        }
      }
      break;
    }
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
  // std::cout << a << std::endl;
  // for (int i = 0; i < vars.size(); i++)
  // {
  //   std::cout << coefficients[i] << " " << vars[i] << std::endl;
  // }
  // for (auto& e : vars) std::cout << e << std::endl;
  // for (auto& e : coefficients) std::cout << e << std::endl;
  return {assertion_kind, coefficients, vars, c, mod_value};
}

mata::nfa::Nfa Automata::build_nfa_for_atomic_formula(const Node& node)
{
  mata::nfa::Nfa aut;
  std::map<NfaState, unsigned int> nfa_state_to_int;
  auto [assertion_kind, coefficients, vars, c, mod_value] =
      get_atomic_formula_structure(node);
  dbg(c);
  unsigned int idx = 0;
  std::cout << "vars_to_int\n";
  for (auto& [a, b] : vars_to_int)
  {
    std::cout << a << " " << b << std::endl;
  }
  switch (assertion_kind)
  {
    case kind::Kind_t::EQUAL:
    {
      NfaState final_state = {0, 1};  // for this particular case we use the mod
                                      // value as a flag for the final state
      std::set<NfaState> states_to_process;

      aut.initial = {idx};
      nfa_state_to_int[{c, mod_value}] = idx++;
      states_to_process.insert({c, mod_value});
      while (!states_to_process.empty())
      {
        // this should remove the first element of the set
        NfaState state = *states_to_process.begin();
        states_to_process.erase(std::next(states_to_process.begin(), 0));

        // I only add the state to the automata if it is not the initial state I
        // already added
        unsigned long number_of_variables =
            static_cast<unsigned long>(vars_to_int.size());
        std::cout << "state being processed\n";
        dbg(state.c);

        for (unsigned long sigma = 0; sigma < (1UL << number_of_variables);
             sigma++)
        {
          int new_c = state.c;

          int acc = 0;
          // this can be preocmputed
          for (int i = 0; i < (int)coefficients.size(); i++)
          {
            acc += coefficients.at(i) * (sigma & (1 << vars_to_int[vars[i]]));
          }
          new_c -= acc;
          if (new_c % 2 != 0) continue;  // value is odd, we can continue
          new_c = divide_by_two_and_floor(new_c);

          if (nfa_state_to_int.count({new_c, state.mod_value}) == 0)
          {
            std::cout << "adding state to aut\n";
            dbg(new_c);
            dbg(idx);
            states_to_process.insert({new_c, state.mod_value});
            aut.add_state(idx);
            nfa_state_to_int[{new_c, state.mod_value}] = idx++;
          }
          aut.delta.add(nfa_state_to_int[{state.c, state.mod_value}],
                        sigma,
                        nfa_state_to_int[{new_c, state.mod_value}]);
          if (state.c + acc >= 0)
          {
            if (aut.final.empty())
            {
              std::cout << "adding final state\n";
              dbg(idx);
              aut.final = {idx};
              nfa_state_to_int[final_state] = idx++;
            }
            aut.delta.add(nfa_state_to_int[{state.c, mod_value}],
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
      std::set<NfaState> states_to_process;

      aut.initial = {idx};
      nfa_state_to_int[{c, mod_value}] = idx++;
      states_to_process.insert({c, mod_value});
      while (!states_to_process.empty())
      {
        // this should remove the first element of the set
        NfaState state = *states_to_process.begin();
        states_to_process.erase(std::next(states_to_process.begin(), 0));

        // I only add the state to the automata if it is not the initial state I
        // already added
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
            acc += coefficients.at(i) * (sigma & (1 << vars_to_int[vars[i]]));
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
            if (aut.final.empty())
            {
              aut.final = {idx};
              nfa_state_to_int[final_state] = idx++;
            }
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

  mata::nfa::Nfa automata;
  to_process.pop_back();  // only removing true formula
  for (const Node a : to_process)
  {
    // build automata for atomic formula
    mata::nfa::Nfa atomic_formula_automata = build_nfa_for_atomic_formula(a);
    atomic_formula_automata.print_to_dot(std::cout);
    // join with general nfa called automata
  }

  std::cout << automata.is_lang_empty() << std::endl;
  return PreprocessingPassResult::NO_CONFLICT;
}

}  // namespace passes
}  // namespace preprocessing
}  // namespace cvc5::internal
