/*
 * Copyright (C) 2013 Magnus Lång
 *
 * This file is part of Memorax.
 *
 * Memorax is free software: you can redistribute it and/or modify it
 * under the terms of the GNU General Public License as published by
 * the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * Memorax is distributed in the hope that it will be useful, but WITHOUT
 * ANY WARRANTY; without even the implied warranty of MERCHANTABILITY
 * or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public
 * License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with this program.  If not, see <http://www.gnu.org/licenses/>.
 *
 */

#include "channel_trie.h"

ChannelTrie::insertion_result ChannelTrie::insert(constr_t constraint) {
  const ChannelConstraint &chc = *constraint;
  const int channel_len = chc.channel.size();

  struct comparison_context {
    ChannelTrie::Node *node;
    int position;
  };

  /* We don't need a comparison_context for equal because the position is always
   * the same as in constraint */
  Node* equal = &roots[channel_len];
  std::list<comparison_context> greater, less;
  for (auto &kvp : roots) {
    if      (kvp.first < channel_len) less   .push_back({&kvp.second, kvp.first - 1});
    else if (kvp.first > channel_len) greater.push_back({&kvp.second, kvp.first - 1});
  }

  std::list<Node *> greater_complete, less_complete;
  std::vector<Node> tmpnodes, old_tmpnodes;

  for (int pos = int(constraint->channel.size()) - 1; pos >= 0; --pos) {
    const msg_t &msg = chc.channel[pos];
    Node *new_equal = nullptr;
    std::list<comparison_context> new_greater, new_less;

    for (comparison_context elem : greater) {
      for (auto &grchild : elem.node->children) {
        Constraint::Comparison cmp =
          Constraint::comb_comp(Constraint::GREATER, grchild.first.entailment_compare(msg));
        if (cmp != Constraint::GREATER && elem.position > pos) {
          /* This message does not match, but the next might. We push the child
           * on greater to be considered against msg again. */
          greater.push_back({grchild.second, elem.position - 1});
        } else if (cmp == Constraint::GREATER) {
          /* The messages match, push the child to be considered against the
           * next message of constraint. */
          new_greater.push_back({grchild.second, elem.position - 1});
        }
      }
    }

    for (comparison_context elem : less) {
      std::map<msg_t, Node*> keepers;
      for (auto &lschild : elem.node->children) {
        Constraint::Comparison cmp =
          Constraint::comb_comp(Constraint::LESS, lschild.first.entailment_compare(msg));
        if (cmp != Constraint::LESS && elem.position < pos) {
          /* The message does not match, but the next msg might. */
          keepers.insert(lschild);
        } else if (cmp == Constraint::LESS && elem.position == 0) {
          /* This constraint is less than constraint and has no more
           * messages. lschild.second presumably refers to a leaf. */
          assert(lschild.second->children.empty());
          less_complete.push_back(lschild.second);
        } else if (cmp == Constraint::LESS) {
          /* The messages match, push the child to be considered against the
           * next message of constraint. */
          new_less.push_back({lschild.second, elem.position - 1});
        }
      }
      if (!keepers.empty()) {
        tmpnodes.push_back({std::move(keepers), {}});
        new_less.push_back({&tmpnodes.back(), elem.position});
      }
    }

    for (auto &eqchild : equal->children)
      switch (eqchild.first.entailment_compare(msg)) {
      case Constraint::EQUAL:   new_equal =        eqchild.second;                break;
      case Constraint::LESS:    new_less   .push_back({eqchild.second, pos - 1}); break;
      case Constraint::GREATER: new_greater.push_back({eqchild.second, pos - 1}); break;
      case Constraint::INCOMPARABLE: /* Do nothing, it doesn't match */           break;
      }
    if (new_equal == nullptr) new_equal = equal->children[msg] = new Node();

    equal = new_equal;
    greater = new_greater;
    less = new_less;
    // Tese are no longer used
    old_tmpnodes.clear();
    tmpnodes.swap(old_tmpnodes);
  }

  assert(less.empty()); // They should all have been moved to less_complete
  /* Dig down in greater to find the leaves. */
  for (comparison_context elem : greater) {
    assert(elem.node->children.empty() || elem.node->constraints.empty());
    if (elem.node->constraints.empty()) {
      for (const auto &grchild : elem.node->children)
        greater.push_back({grchild.second, elem.position - 1});
    } else {
       assert(elem.position == 0);
       greater_complete.push_back(elem.node);
    }
  }

  insertion_result result;
  /* We check if any constraint in less is really less than constraint. */
  for (Node *node : less_complete) {
    for (const constr_t &lsconstr : node->constraints) {
      Constraint::Comparison cmp = lsconstr->entailment_compare(chc);
      result.comparison_count++;
      if (cmp == Constraint::LESS) {
        /* constraint is subsumed by lsconstr */
        result.was_subsumed = true;
        result.deleted.push_back(std::move(constraint));
        return result;
      } else {
        assert(cmp == Constraint::INCOMPARABLE);
      }
    }
  }
  for (int i = 0; i < int(equal->constraints.size()); ++i) {
    Constraint::Comparison cmp = equal->constraints[i]->entailment_compare(chc);
    result.comparison_count++;
    if (cmp == Constraint::LESS || cmp == Constraint::EQUAL) {
      /* constraint is subsumed by equal->constraints[i] */
      result.was_subsumed = true;
      assert(result.deleted.empty());
      result.deleted.push_back(std::move(constraint));
      return result;
    } else if (cmp == Constraint::GREATER) {
      /* constraint subsumes equal->constraints[i] */
      result.deleted.push_back(remove_from_vector(equal->constraints, i--));
    }
  }
  /* We know for sure that constraint is not subsumed by any other in this
   * trie. We insert it into equal. */
  equal->constraints.push_back(std::move(constraint));
  for (Node *node : greater_complete) {
    for (int i = 0; i < int(node->constraints.size()); ++i) {
      Constraint::Comparison cmp = node->constraints[i]->entailment_compare(chc);
      result.comparison_count++;
      if (cmp == Constraint::GREATER) {
        /* constraint subsumes node->constraints[i] */
        result.deleted.push_back(remove_from_vector(equal->constraints, i--));
      } else {
        assert(cmp == Constraint::INCOMPARABLE);
      }
    }
  }

  return result;
};

ChannelTrie::constr_t ChannelTrie::remove_from_vector(std::vector<constr_t> &v, int index) const {
  constr_t c = std::move(v[index]);
  v[index] = std::move(v.back());
  v.pop_back();
  return c;
}
