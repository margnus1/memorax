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

#ifndef __CHANNEL_CONTAINER__
#define __CHANNEL_CONTAINER__

#include "constraint_container.h"
#include "sb_constraint.h"
#include "ticket_queue.h"
#include "channel_trie.h"

/* A constraint container meant for ChannelConstraints. Uses
 * ChannelConstraint::entailment_compare for comparison and entailment upon
 * insertion.
 */
class ChannelContainer : public ConstraintContainer{
public:
  ChannelContainer();
  virtual ~ChannelContainer();

  virtual void insert_root(Constraint *r);
  virtual void insert(Constraint *p, const Machine::PTransition *t, Constraint *c);
  virtual Constraint *pop();
  virtual int Q_size() const { return q_size; };
  virtual int F_size() const { return f_size; };
  virtual Trace *clear_and_get_trace(Constraint *c);
  virtual void clear();
protected:
  /* Keeps a ChannelConstraint and some extra information about it. */
  struct CWrapper{
    CWrapper(ChannelConstraint *chc, CWrapper *parent = 0, const Machine::PTransition *pt = 0)
      : chc(chc), parent(parent), p_transition(pt), valid(true) {};
    ~CWrapper(){
      if(chc){
        delete chc;
      }
    };
    /* The constraint itself */
    ChannelConstraint *chc;
    /* The wrapper around the parent of chc.
     * Null if chc is a root constraint. */
    CWrapper *parent;
    /* The transition by which parent transitioned into chc.
     * Null if parent is null.
     *
     * The transition is not owned by the CWrapper. The pointer points
     * to some transition which ownership lies outside of the
     * ChannelContainer. (Most likely in
     * Chconstraint::Common::all_transitions.)
     */
    const Machine::PTransition *p_transition;
    /* A vector containing pointers to all CWrappers cw such that
     * cw.parent == this 
     * 
     * Only kept up-to-date if use_genealogy == true. */
    std::vector<CWrapper*> children;
    /* False iff this constraint has been subsumed, and should not be
     * considered part of Q. */
    bool valid;
    /* The ticket of this constraint in Q */
    long Q_ticket;
  };
  typedef std::unique_ptr<CWrapper> OwnedCWrapper;

  /* F is partitioned by some property p(c) of a constraint c such that p(a) !=
   * p(b) only if a and b are incomparable.  
   * 
   * The partition sets are represented as distinct, unordered vectors.  In
   * order to allow changing the property p via inheritance, access to F must be
   * done through get_F_set(c) which returns the partition set of c and visit_F(f)
   * which calls f(S) on each non-empty partition set S. */
  virtual ChannelTrie<CWrapper> &get_F_set(CWrapper *);
  virtual void visit_F(std::function<void(ChannelTrie<CWrapper>&)>);

private:
  /* F[pcs][chr] maps to the set of all constraints in F that have
   * program counters pcs and channel characterization chr.
   *
   * The sets are represented as distinct, unordered vectors.
   */
 std::map<std::vector<int>,std::map<std::vector<ChannelConstraint::MsgCharacterization> , ChannelTrie<CWrapper> > > F;
  /* Stores pointers to the wrappers that have been invalidated. They
   * should not be considered in the analysis, but should be
   * deallocated upon destruction of the container. */
  std::vector<OwnedCWrapper> invalid_from_F;
  
  /* For each constraint c in F, ptr_to_F[c] is a pointer to its
   * CWrapper in F.
   */
  std::map<ChannelConstraint*,CWrapper*> ptr_to_F;

  /* Caches (chc,cw) for the last constraint chc that was popped, and
   * cw == ptr_to_F[chc].
   */
  std::pair<ChannelConstraint*,CWrapper*> last_popped;

  /* Returns ptr_to_F[chc]. Uses the cache last_popped if possible.
   */
  CWrapper *get_cwrapper(ChannelConstraint *chc) const{
    if(last_popped.first == chc){
      return last_popped.second;
    }else{
      return ptr_to_F.at(chc);
    }
  };

  /* ChannelPrioTicketQueue is the class for Q.
   *
   * It uses multiple TicketQueues to implement a queue where priority
   * is given to shorter channels. */
  class ChannelPrioTicketQueue{
  public:
    long push(CWrapper *cw){
      if(int(queues.size()) <= cw->chc->get_weight()){
        queues.resize(cw->chc->get_weight()+1);
      }
      return queues[cw->chc->get_weight()].push(cw);
    };
    CWrapper *pop(){
      /* Give priority to shorter channels. */
      for(unsigned i = 1; i < queues.size(); ++i){
        if(queues[i].size() > 0){
          return queues[i].pop();
        }
      }
      return 0;
    };
    bool in_queue(long tck,int chan_len){
      return queues[chan_len].in_queue(tck);
    };
    void clear(){
      for(unsigned i = 0; i < queues.size(); ++i){
        queues[i].clear();
      }
      queues.clear();
    };
  private:
    /* queues[i] contains the constraints whose channel has length i. */
    std::vector<TicketQueue<CWrapper*> > queues;
  };

  /* The queue.
   * 
   * Pointers are to objects shared with F. Q does not have
   * ownership. */
  ChannelPrioTicketQueue Q;

  bool insert(OwnedCWrapper cw);

  /* The number of valid constraints in F */
  int f_size;
  /* The number of valid constraints in Q */
  int q_size;

  /* Set cw->valid = false, remove it from Q.
   *
   * If use_genealogy, recursively do the same for all children of cw, and
   * delete them from F.
   */
  void invalidate(OwnedCWrapper cw);

#ifndef NDEBUG
  struct stats_t{
    stats_t()
      : longest_channel(0),
        most_comparisons(0),
        invalidate_count(0) {};
    int longest_channel;
    int most_comparisons;
    int invalidate_count;
    void print(){
      Log::debug << " ===============================\n"
                 << " = ChannelContainer statistics =\n"
                 << " ===============================\n"
                 << " heaviest constraint: " << longest_channel << "\n"
                 << " most comparisons: " << most_comparisons << "\n"
                 << " invalidated: " << invalidate_count << "\n";
    };
  };

  stats_t stats;
#endif
  void update_longest_channel(int chanlen){
#ifndef NDEBUG
    stats.longest_channel = std::max(chanlen,stats.longest_channel);
#endif
  };
  void update_most_comparisons(int comparisons){
#ifndef NDEBUG
    stats.most_comparisons = std::max(comparisons, stats.most_comparisons);
#endif
  };
  void inc_invalidate_count(){
#ifndef NDEBUG
    ++stats.invalidate_count;
#endif
  };

  static const bool print_every_state_on_clear;
  static const bool use_genealogy;
};

#endif
