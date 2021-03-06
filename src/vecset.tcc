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


template<class T>
int VecSet<T>::find_geq(const T &t) const{
  /* Use binary search */
  int a = 0;
  int b = vec.size();
  while(a < b){
    int c = (a+b)/2;
    if(vec[c] < t){
      a = c+1;
    }else if(vec[c] == t){
      return c;
    }else{
      b = c;
    }
  }
  return a;
};

template<class T>
int VecSet<T>::find(const T &t) const{
  int i = find_geq(t);
  if(i == int(vec.size()) || !(vec[i] == t)){
    return -1;
  }else{
    return i;
  }
};

template<class T>
int VecSet<T>::count(const T &t) const{
  if(find(t) >= 0){
    return 1;
  }else{
    return 0;
  }
};

template<class T>
std::pair<int,bool> VecSet<T>::insert(const T &t){
  int i = find_geq(t);
  if(i < int(vec.size()) && vec[i] == t){
    /* t is already in the set */
    return std::pair<int,bool>(i,false);
  }else{
    if(vec.size() == 0){
      vec.push_back(t);
    }else{
      vec.push_back(vec.back());
      for(int j = vec.size()-2; j > i; j--){
        vec[j] = vec[j-1];
      }
      vec[i] = t;
    }
    return std::pair<int,bool>(i,true);
  }
};

template<class T>
int VecSet<T>::insert(const VecSet<T> &s){
  if(s.size() == 0){
    return 0;
  }else if(s.size() == 1){
    return (insert(s[0]).second ? 1 : 0);
  }else{
    /* Count the number of elements that are in s but not in this set */
    int count = 0;

    int a = 0; // pointer into this set
    int b = 0; // pointer into s
    while(a < size() && b < s.size()){
      if(vec[a] < s.vec[b]){
        ++a;
      }else if(vec[a] == s.vec[b]){
        ++a;
        ++b;
      }else{
        ++count;
        ++b;
      }
    }
    if(b < s.size()){
      assert(a == size());
      count += s.size() - b;
    }

    if(count > 0){
      a = int(vec.size())-1;
      b = int(s.vec.size())-1;
      vec.resize(vec.size() + count,s.vec[0]);
      /* Insert one-by-one the largest remaining element from this union s */
      for(int i = int(vec.size())-1; i >= 0; i--){
        assert(i >= a);
        if(a < 0 || (b >= 0 && vec[a] < s.vec[b])){
          vec[i] = s.vec[b];
          --b;
        }else if(a >= 0 && b >= 0 && vec[a] == s.vec[b]){
          vec[i] = vec[a];
          --a;
          --b;
        }else{
          assert(a >= 0);
          assert(b < 0 || s.vec[b] < vec[a]);
          vec[i] = vec[a];
          --a;
        }
      }
      assert(a == -1 && b == -1);
    }

    return count;
  }
};

template<class T>
bool VecSet<T>::check_invariant() const{
  for(unsigned i = 1; i < vec.size(); ++i){
    if(!(vec[i-1] < vec[i])){
      return false;
    }
  }
  return true;
};

inline void test_vecset_int(){
  /* Test 1: insert(set): Empty */
  {
    VecSet<int> A;
    VecSet<int> B;
    VecSet<int> AB_target;
    VecSet<int> AB = A;
    AB.insert(B);
    VecSet<int> BA = B;
    BA.insert(A);
    if(AB == AB_target && BA == AB_target){
      std::cout << "Test1: Success!\n";
    }else{
      std::cout << "Test1: Failure\n";
    }
  }

  /* Test 2: insert(set) */
  {
    VecSet<int> A;
    A.insert(2); A.insert(5); A.insert(42); A.insert(113);
    VecSet<int> B;
    B.insert(2); B.insert(7); B.insert(79); B.insert(42);
    VecSet<int> AB_target;
    AB_target.insert(2); AB_target.insert(5); AB_target.insert(7); AB_target.insert(42);
    AB_target.insert(79); AB_target.insert(113);
    VecSet<int> AB = A;
    AB.insert(B);
    VecSet<int> BA = B;
    BA.insert(A);
    if(AB == AB_target && BA == AB_target){
      std::cout << "Test2: Success!\n";
    }else{
      std::cout << "Test2: Failure\n";
    }
  }
};

template<class T>
std::string VecSet<T>::to_string_one_line(std::function<std::string(const T&)> &f) const{
  std::string s = "{";
  for(unsigned i = 0; i < vec.size(); ++i){
    if(i != 0) s += ", ";
    s += f(vec[i]);
  }
  s += "}";
  return s;
};

template<class T>
bool VecSet<T>::subset_of(const VecSet<T> &s) const{
  if(vec.size() > s.vec.size()){
    return false;
  }
  int a = 0; // pointer into vec
  int b = 0; // pointer into s.vec
  while(a < int(vec.size())){
    if((int(vec.size()) - a) > (int(s.vec.size()) - b)){
      return false;
    }
    if(vec[a] < s.vec[b]){
      return false;
    }else if(vec[a] == s.vec[b]){
      ++a;
      ++b;
    }else{
      ++b;
    }
  }
  return true;
};

template<class T>
bool VecSet<T>::intersects(const VecSet<T> &s) const{
  int a = 0; // pointer into vec
  int b = 0; // pointer into s.vec
  while(a < int(vec.size()) && b < int(s.vec.size())){
    if(vec[a] < s.vec[b]){
      ++a;
    }else if(vec[a] == s.vec[b]){
      return true;
    }else{
      ++b;
    }
  }
  return false;
};
