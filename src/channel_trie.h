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

#ifndef __CHANNEL_TRIE_H__
#define __CHANNEL_TRIE_H__

#include "channel_constraint.h"

/* Trie data structure for storing a minor set of constraints with
 * subsuming insert. */
class ChannelTrie {
private:
  typedef ChannelConstraint::Msg                   msg_t;
  typedef std::unique_ptr<const ChannelConstraint> constr_t;
  struct Node {
    std::map<msg_t, Node*> children;
    std::vector<constr_t>  constraints;
    // Node* parent; // Is this needed?
  };

  /* We map channel length to the trie where the constraints with that channel
   * length are stored. */
  std::map<int, Node> roots;
public:
  ChannelTrie() = default;
  ~ChannelTrie();

  struct insertion_result {
    int comparison_count;
    /* Wether the inserted constraint was subsumed. */
    bool was_subsumed;
    /* All constraints that were subsumed by the inserted constraint and
     * removed. If was_subsumed, contains only the constraint that was being
     * inserted. */
    std::vector<constr_t> deleted;
  };

  insertion_result insert(constr_t constraint);

  typedef std::function<void(constr_t)> visitor_func;
  void visit(visitor_func func);

private:
  /* Removes and returns a constr_t from v at index index. Preserves the
   * contents of elements with indices lower than index. */
  constr_t remove_from_vector(std::vector<constr_t> &v, int index) const;
};

#endif
