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

#include "pws_constraint.h"
#include <iostream>

PwsConstraint::Common::Common(const Machine &m) : SbConstraint::Common(m) {
  /* Messages contains every memory location that is ever written
   * We insert serialise transitions for that memory location and the writing process
   * at each state. */
  for (const SbConstraint::Common::MsgHdr &header : messages) {
    int p = header.wpid;
    if (header.nmls.size() > 0) { //We are not interested in the dummy message
      const std::vector<Automaton::State> &states = machine.automata[p].get_states();
      for (unsigned i = 0; i < states.size(); i++) {
        VecSet<Lang::MemLoc<int>> mls;
        for (const Lang::NML &nml : header.nmls)
          mls.insert(nml.localize(p));
        // TODO: Does this risk breaking memory address references to the elements of transitions_to_pc (and possibly others)?
        all_transitions.push_back(Machine::PTransition(i, Lang::Stmt<int>::serialise(mls), i, p));
        transitions_by_pc[p][i].push_back(&(all_transitions[all_transitions.size() - 1]));
      }
    }
  }
  // TODO: make last_msgs work for PSO (currently disabled)
  // TODO: Ponder if can_have_pending needs modification
  //throw new std::logic_error("PwsConstraint::Common::Common: Not implemented");
}

std::list<Constraint*> PwsConstraint::Common::get_bad_states() {
  // Upgrade each SbConstraint to a PwsConstraint
  std::list<Constraint*> l = SbConstraint::Common::get_bad_states();
  for (Constraint *&c : l) {
    SbConstraint *sbc = dynamic_cast<SbConstraint*>(c);
    /* This constraint will have empty write buffers, but can generate arbitrary write buffers
       by serialising "lost" write messages in the channel. */
    c = new PwsConstraint(*sbc, *this);
    delete sbc;
  }
  return l;
};

PwsConstraint::PwsConstraint(std::vector<int> pcs, const SbConstraint::Common::MsgHdr &msg, Common &c) :
    SbConstraint(pcs, msg, c), common(c) {
  for (unsigned p = 0; p < common.machine.automata.size(); p++)
    write_buffers.push_back(std::vector<Store>(common.mem_size, Store(0)));
}

PwsConstraint::PwsConstraint(const SbConstraint &s, Common &c) 
  : SbConstraint(s), common(c) {
  for (unsigned p = 0; p < common.machine.automata.size(); p++)
    write_buffers.push_back(std::vector<Store>(common.mem_size, Store(0)));
};

std::list<Constraint*> PwsConstraint::pre(const Machine::PTransition &t) const {
  std::list<Constraint*> res;
  const Lang::Stmt<int> &s = t.instruction;
  if (SbConstraint::pcs[t.pid] != t.target)
    return res;

  switch (s.get_type()) {
  case Lang::NOP/* 0 */: {
    PwsConstraint *pwsc = new PwsConstraint(*this);
    pwsc->pcs[t.pid] = t.source;
    res.push_back(pwsc);
  } break;

  case Lang::READASSERT/* 3 */: {
    Lang::NML nml(s.get_memloc(), t.pid);
    int nmli = common.index(nml);
    int msgi = index_of_read(nml, t.pid);
    VecSet<int> val_nml;
    int buffer_size = write_buffers[t.pid][nmli].size();
    if (buffer_size > 0) {
      auto bufferValue = write_buffers[t.pid][nmli][buffer_size - 1];
      val_nml = possible_values(bufferValue, nml);
    } else {
      val_nml = SbConstraint::possible_values(channel[msgi].store, nml);
    }
    for (int i = 0; i < val_nml.size(); i++) {
      /* For each possible value for nml, try to pair it with an
       * assignment to the reg_store such that s.expr() evaluates to
       * the same value. */
      VecSet<Store> stores = possible_reg_stores(reg_stores[t.pid], t.pid, s.get_expr(), val_nml[i]);
      for (int j = 0; j < stores.size(); ++j) {
        PwsConstraint *pwsc = new PwsConstraint(*this);
        pwsc->pcs[t.pid] = t.source;
        if (buffer_size > 0) pwsc->write_buffers[t.pid][nmli].assign(buffer_size - 1, val_nml[i]);
        else pwsc->channel[msgi].store = channel[msgi].store.assign(nmli, val_nml[i]);
        pwsc->reg_stores[t.pid] = stores[j];
        res.push_back(pwsc);
      }
    }
  } break;

  case Lang::WRITE /* 5 */: {
    
    
  } break;

  case Lang::UPDATE/* 8 */: {
    // Hmm, this is just copy-and-paste code reuse; could we use the code in SbConstraint::pre instead?
    VecSet<Lang::NML> snmls;
    for (Lang::MemLoc<int> ml : s.get_writes()) 
      snmls.insert(Lang::NML(ml, t.pid));
    /* Check that the message matches the update */
    if (channel[cpointers[t.pid]].wpid == s.get_writer() &&
        channel[cpointers[t.pid]].nmls == snmls) {
      if (cpointers[t.pid] == 0) {
        /* Need to insert a fresh message. */
        for (const SbConstraint::Common::MsgHdr &hdr : common.messages) {
          PwsConstraint *pwsc = new PwsConstraint(*this);
          Msg msg(Store(common.mem_size), hdr.wpid, hdr.nmls);
          pwsc->channel.insert(pwsc->channel.begin(), msg);
          for (int p = 0; p < pwsc->cpointers.size(); p++) {
            if (p != t.pid) pwsc->cpointers[p]++;
          }
        }
      } else {
        /* Update with a message in the channel */
        PwsConstraint *pwsc = new PwsConstraint(*this);
        pwsc->cpointers[t.pid]--;
        res.push_back(pwsc);
      }
    }
  } break;
    
  case Lang::SERIALISE /* 9 */: {
    int pid = t.pid;
    assert(s.get_writes().size() == 1);
    Lang::NML nml(s.get_writes()[0], pid);
    int nmli = common.index(nml);
    uint maxcptr = *std::max_element(cpointers.begin(), cpointers.end());
    /* All hell breaks loose if we allow writes to more than one place at
     * once. Sureley that cant be required! */
    assert(channel.back().nmls.size() == 1); 
    /* We can only do serialise if the last message has the right process and
     * memory locations and isn't pointed to by any cpointer. */
    if (maxcptr < channel.size() - 1 && channel.back().wpid == pid && 
        channel.back().nmls[0] == nml) {
      PwsConstraint *pwsc = new PwsConstraint(*this);
      /* TODO: Consider if we need to add constraints where a "lost" constraint
       * preceeds the last message. Hmm, is this what channel_pop_back does? */
      pwsc->channel.pop_back();
      pwsc->write_buffers[pid][nmli] = pwsc->write_buffers[pid][nmli].push_front(channel.back().store[nmli]);
    }
  } break;

  default:
    //Log::debug << "Received unknown type of statement: " << s.get_type() << "\n";
    std::stringstream ss;
    ss << "PwsConstraint::pre: Unknown statement type " << s.get_type() << " not implemented\n";
    throw new std::logic_error(ss.str());
  }
  return res;
}

std::string PwsConstraint::to_string() const throw() {
  std::stringstream ss(SbConstraint::to_string());
  for (uint p = 0; p < common.machine.automata.size(); p++) {
    ss << "P" << p << " buffer={";
    for (int g = 0; g < common.gvar_count; g++) {
      pretty_print_buffer(ss, write_buffers[p], Lang::NML::global(g));
    }
    ss << "}\n";
  }
  return ss.str();
}

void PwsConstraint::pretty_print_buffer(std::stringstream &ss, const std::vector<Store> &buffer,
                                        Lang::NML nml) const {
  int nmli = common.index(nml);
  if (buffer[nmli].size() == 0) return;
  ss << common.machine.pretty_string_nml.at(nml) << ": ";
  for (int i = 0; i < buffer[nmli].size(); i++)
    if (buffer[nmli][i].is_star()) ss << "*,";
    else ss << buffer[nmli][i].get_int() << ",";
  ss << "; ";
}

Constraint::Comparison PwsConstraint::entailment_compare(const SbConstraint &sbc) const{
  const PwsConstraint &pwsc = dynamic_cast<const PwsConstraint&>(sbc);
  return entailment_compare(pwsc);
}

Constraint::Comparison PwsConstraint::entailment_compare(const PwsConstraint &pwsc) const{
  Constraint::Comparison cmp = SbConstraint::entailment_compare(pwsc);
  if (cmp == Constraint::INCOMPARABLE) return cmp;
  return comb_comp(entailment_compare_buffers(pwsc), cmp);
}

Constraint::Comparison PwsConstraint::entailment_compare_buffers(const PwsConstraint &pwsc) const{
  Comparison cmp = EQUAL;
  for (int p = 0; p < common.machine.proc_count(); p++) {
    for (int ml = 0; ml < common.mem_size; ml++) {
      cmp = comb_comp(entailment_compare_buffer(write_buffers[p][ml], pwsc.write_buffers[p][ml]), cmp);
      if (cmp == Constraint::INCOMPARABLE) return cmp;
    }
  }
  return cmp;
}

Constraint::Comparison PwsConstraint::entailment_compare_buffer(const Store& a, const Store& b) const{
  if (a.size() == b.size()) {
    return a.entailment_compare(b);
  } else if (a.size() > b.size()) {
    return invert_comp(entailment_compare_buffer(b, a));
  }
  // a is either LESS than b, or INCOMPARABLE.
  if (a.size() == 0) return INCOMPARABLE; // a must be empty iff b is
  // a and b must end with the same value
  if (a[a.size() - 1] != b[b.size() - 1] && a[a.size() - 1] != value_t::STAR) return INCOMPARABLE;
  // We check if a is a subword of b
  for (int ai = 0, bi = 0; ai < a.size(); bi++) {
    if (bi == b.size()) return INCOMPARABLE; // a isn't a subword of b
    if (a[ai] == b[bi] || a[ai] == value_t::STAR) //TODO: Ponder the correctness of this
      ai++; // They match
  }
  return LESS; // a is a subword of b
}
