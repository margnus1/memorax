/*
 * Copyright (C) 2012 Carl Leonardsson
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

#include "channel_container.h"

const bool ChannelContainer::print_every_state_on_clear = false;
const bool ChannelContainer::use_genealogy = false;

ChannelContainer::ChannelContainer(){
  last_popped.first = 0;
  last_popped.second = 0;
  q_size = f_size = 0;
};

ChannelContainer::~ChannelContainer(){
#ifndef NDEBUG
  stats.print();
#endif
  clear();
};

void ChannelContainer::insert_root(Constraint *r){
  insert(OwnedCWrapper(new CWrapper(static_cast<ChannelConstraint*>(r))));
};

void ChannelContainer::insert(Constraint *p, const Machine::PTransition *t, Constraint *c){
  CWrapper *pcw = get_cwrapper(static_cast<ChannelConstraint*>(p));
  OwnedCWrapper cw(new CWrapper(static_cast<ChannelConstraint*>(c), pcw, t));
  CWrapper *cwp = cw.get();
  if(insert(std::move(cw))){
    if(use_genealogy){
      pcw->children.push_back(cwp);
    }
  }
};

bool ChannelContainer::insert(OwnedCWrapper cw){
  CWrapper *ptr = cw.get();
  assert(ptr);
  ChannelTrie<CWrapper> &v = get_F_set(cw.get());
  ChannelTrie<CWrapper>::insertion_result res = v.insert(std::move(cw));

  if (res.was_subsumed) return false;

  for (OwnedCWrapper &cw : res.deleted)
    invalidate(std::move(cw));

  update_most_comparisons(res.comparison_count);
  update_longest_channel(ptr->chc->get_weight());
  ptr_to_F[ptr->chc] = ptr;
  ptr->Q_ticket = Q.push(ptr);
  ++q_size;
  ++f_size;
  return true;
};

void ChannelContainer::invalidate(OwnedCWrapper cw){
  cw->valid = false;
  if(Q.in_queue(cw->Q_ticket, cw->chc->get_weight())){
    --q_size;
  }
  --f_size;
  inc_invalidate_count();
  if(use_genealogy){
    for(CWrapper *child : cw->children){
      if(child->valid){
        invalidate(get_F_set(child).remove(child));
      }
    }
  }
  invalid_from_F.push_back(std::move(cw));
};

Constraint *ChannelContainer::pop(){
  if(q_size == 0){
    return 0;
  }else{
    CWrapper *cw = Q.pop();
    while(!cw->valid){
      cw = Q.pop();
    }
    --q_size;
    last_popped.first = cw->chc;
    last_popped.second = cw;
    return cw->chc;
  }
};

Trace *ChannelContainer::clear_and_get_trace(Constraint *c){
  Trace *t = new Trace(c);
  CWrapper *cw = get_cwrapper(static_cast<ChannelConstraint*>(c));
  cw->chc = 0;
  while(cw->parent){
    t->push_back(*cw->p_transition,cw->parent->chc);
    cw->parent->chc = 0;
    cw = cw->parent;
  }
  clear();
  return t;
};

void ChannelContainer::clear(){
  if(print_every_state_on_clear){
    Log::extreme << "  **************************************\n";
    Log::extreme << "  *** All constraints in visited set ***\n";
    Log::extreme << "  **************************************\n\n";
  }
  if(print_every_state_on_clear){
    visit_F([](ChannelTrie<CWrapper> &S) {
        S.visit([](const CWrapper *cw) {
            if(cw->chc){
              Log::extreme << cw->chc->to_string() << "\n";
            }
          });
      });
  }
  invalid_from_F.clear();
  F.clear();
  Q.clear();
  ptr_to_F.clear();
  f_size = 0;
  q_size = 0;
  last_popped.first = 0;
  last_popped.second = 0;
};

ChannelTrie<ChannelContainer::CWrapper> &ChannelContainer::get_F_set(CWrapper *cw){
  return F[cw->chc->get_control_states()][cw->chc->characterize_channel()];
}

void ChannelContainer::visit_F(std::function<void(ChannelTrie<CWrapper>&)> f){
  for(auto &FPerPcs : F){
    for (auto &subset : FPerPcs.second){
      f(subset.second);
    }
  }
}
