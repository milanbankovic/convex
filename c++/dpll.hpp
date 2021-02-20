#ifndef _DPLL_H_
#define _DPLL_H_

/* DPLL BASED SAT SOLVER */

#include <cassert>
#include <iostream>
#include <vector>
#include <utility>
#include <functional>
#include <algorithm>
#include <unordered_map>

typedef unsigned variable;  

typedef unsigned literal;

enum polarity { P_POSITIVE, P_NEGATIVE };

inline
literal lit_from_var(variable v, polarity p)
{
  return p == P_POSITIVE ? v << 1 : (v << 1) | 1;
}

inline
variable var_from_lit(literal l)
{
  return l >> 1;
}

inline
bool is_positive(literal l)
{
  return !(l & 1);
}

inline
bool is_negative(literal l)
{
  return l & 1;
}

inline
literal opposite_literal(literal l)
{
  return l ^ 1;
}

inline
int int_from_lit(literal l)
{
  return is_positive(l) ? (int)var_from_lit(l) + 1 : -(int)(var_from_lit(l) + 1);
}

inline
literal lit_from_int(int i)
{
  return i > 0 ? lit_from_var(i - 1, P_POSITIVE) : lit_from_var(-i - 1, P_NEGATIVE);
}

typedef std::vector<literal> clause;

enum extended_boolean {
  B_FALSE = -1,
  B_UNDEFINED = 0,
  B_TRUE = 1
};

inline
extended_boolean operator ! (extended_boolean eb)
{
  return (extended_boolean)(-eb);
}

class valuation {
private:
  std::vector<extended_boolean> _values;
  std::vector< std::pair<literal, unsigned> > _stack;
  unsigned _curr_level;
public:
  valuation(unsigned num_of_vars)
    :_values(num_of_vars, B_UNDEFINED),
     _curr_level(0)
  {}

  literal operator [] (unsigned i) const
  {
    return _stack[i].first;
  }
  
  unsigned num_of_vars() const
  {
    return _values.size();
  }
  
  unsigned current_level() const
  {
    return _curr_level;
  }

  unsigned stack_size() const
  {
    return _stack.size();
  }

  void push(literal l, bool decide = false)
  {
    if(decide)
      _curr_level++;

    _stack.push_back({ l, _curr_level });
    _values[var_from_lit(l)] = is_positive(l) ? B_TRUE : B_FALSE;
  }

  void clear()
  {
    _stack.clear();
    _values.assign(_values.size(), B_UNDEFINED);
    _curr_level = 0;
  }
  
  literal backtrack()
  {
    literal l;
    while(!_stack.empty() && _stack.back().second == _curr_level)
      {
	_values[var_from_lit(_stack.back().first)] = B_UNDEFINED;
	l = _stack.back().first;
	_stack.pop_back();
      }
    _curr_level--;
    return l;
  }

  extended_boolean variable_value(variable v) const
  {
    return _values[v];
  }

  extended_boolean literal_value(literal l) const
  {
    return is_positive(l) ? 
      _values[var_from_lit(l)] : 
      !_values[var_from_lit(l)];
  }
  
  void print_stack(std::ostream & ostr) const
  {
    unsigned level  = 0;
    for(unsigned i = 0; i < _stack.size(); i++)
      {
	if(_stack[i].second > level)
	  {
	    ostr << "| ";
	    level++;
	  }
	ostr << int_from_lit(_stack[i].first)  << " ";
      }
    ostr << std::endl;
  }
};


void print_clause(const clause & c, std::ostream & ostr)
{
  ostr << "[ ";
  for(clause::const_iterator i = c.begin(); i != c.end(); i++)
    ostr << int_from_lit(*i) << " ";
  ostr << "]";
}


inline
std::ostream & operator << (std::ostream & ostr, const clause & cl)
{
  print_clause(cl, ostr);
  return ostr;
}


class solver {
private:
  valuation _val;
  std::vector< std::vector<clause *> > _watch_lists;
  bool _conflict = false;
  unsigned _pending_pos = 0;
  unsigned _next_decision = 0;
  bool _next_model = false;
  
  std::vector< clause * > _long_clauses;
  std::vector< literal > _units;
  std::vector< unsigned > _long_clauses_contexts;
  std::vector< unsigned > _units_contexts;

  std::vector< std::vector<clause *> > _inactive_lists;

  unsigned _empty_clause_context = (unsigned)(-1);


  //unsigned long _decide_count = 0;
  //unsigned long _backtrack_count = 0;
  //unsigned long _num_solve = 0;

  
public:
  solver(unsigned num_of_vars)
    :_val(num_of_vars),
     _watch_lists(num_of_vars << 1),
     _inactive_lists(num_of_vars << 1)
  {}

  solver(const solver &) = delete;
  solver(solver &&) = delete;

  const valuation & val() const
  {
    return _val;
  }

  void add_clause_context()
  {
    _long_clauses_contexts.push_back(_long_clauses.size());
    _units_contexts.push_back(_units.size());
  }

  void add_clauses(std::vector<clause> & clauses)
  {
    for(unsigned k = 0; k < clauses.size(); k++)
      {	
	clause & cl = clauses[k];

	if(cl.size() == 0)
	  {
	    _conflict = true;
	    _empty_clause_context = _long_clauses_contexts.size();
	    return;
	  }
	
	if(cl.size() == 1)
	  {
	    _units.push_back(cl[0]);
	    continue;
	  }
	    
	_long_clauses.push_back(&cl);
	_inactive_lists[cl[0]].push_back(&cl);
      }
  }

  unsigned num_of_watched_clauses()
  {
    unsigned count = 0;
    for(unsigned k = 0; k < _watch_lists.size(); k++)
      {
	count += _watch_lists[k].size();
      }
    return count;    
  }

  unsigned num_of_inactive_clauses()
  {
    unsigned count = 0;
    for(unsigned k = 0; k < _inactive_lists.size(); k++)
      count += _inactive_lists[k].size();

    return count;    
  }
  
  void restore_clause_context(unsigned k)
  {
    if(k >= _long_clauses_contexts.size())
      return;
 
    while(_long_clauses.size() > _long_clauses_contexts[k])
      {
	clause & cl = *_long_clauses.back();
	std::vector<clause *> & wlist0 = _watch_lists[cl[0]];	    
	auto it0 = std::find(wlist0.begin(), wlist0.end(), &cl);
	if(it0 == wlist0.end())
	  {
	    std::vector<clause *> & ilist = _inactive_lists[cl[0]];
	    ilist.erase(std::find(ilist.begin(), ilist.end(), &cl));
	  }
	else
	  {
	    wlist0.erase(it0);
	    std::vector<clause *> & wlist1 = _watch_lists[cl[1]];
	    wlist1.erase(std::find(wlist1.begin(), wlist1.end(), &cl));
	  }      
	_long_clauses.pop_back();
      }
    _long_clauses_contexts.resize(k);
    
    _units.resize(_units_contexts[k]);
    _units_contexts.resize(k);
    
    if(_empty_clause_context > _long_clauses_contexts.size())
      _empty_clause_context = (unsigned)(-1);
  }

  void initialize_solver()
  {
    if(_empty_clause_context > _long_clauses_contexts.size())
      _conflict = false;

    _next_model = false;
    _pending_pos = 0;
    _next_decision = 0;
    _val.clear();
  }
  
  void set_units()
  {
    for(unsigned i = 0; i < _units.size(); i++)
      {
	literal l = _units[i];
	
	extended_boolean b = _val.literal_value(l);
	if(b == B_FALSE)
	  {
	    _conflict = true;
	    return;
	  }
	else if(b == B_UNDEFINED)
	  {
	    apply_unit_propagation(l);
	  }
      } 
  }
  
  void set_watch_lists()
  {    
    for(literal l = 0; l < _inactive_lists.size(); l++)
      {
	if(_val.literal_value(l) == B_TRUE)
	  continue;
	
	std::vector<clause *> & l_list = _inactive_lists[l];

	unsigned j = 0;
	for(unsigned k = 0; k < l_list.size(); k++)
	  {
	    clause & cl = *l_list[k];
	    	    
	    unsigned i;
	    bool found_undef = false;
	    extended_boolean b;
	    
	    for(i = 0; i < cl.size() && (b = _val.literal_value(cl[i])) != B_TRUE; i++)
	      {
		if(b == B_UNDEFINED)
		  found_undef = true;
	      }
	    
	    if(i < cl.size())
	      {
		std::swap(cl[0], cl[i]);
		_inactive_lists[cl[0]].push_back(&cl);

		continue;
	      }
	    
	    if(found_undef == false)
	      {
		_conflict = true;
		for(; k < l_list.size(); k++)
		  l_list[j++] = l_list[k];
		return;
	      }
	    
	    _watch_lists[cl[0]].push_back(&cl);
	    _watch_lists[cl[1]].push_back(&cl);	
	  }
	l_list.resize(j);
      }
  }

  void simplify_clauses()
  {
    check_conflict_and_propagations();
    if(!_conflict)
      simplify();
  }
  
  bool find_alternative_watch(clause * cl, unsigned & i)
  {
    for(i = 2; i < cl->size(); i++)
      {	
	if(_val.literal_value((*cl)[i]) != B_FALSE)
	  return true;
      }
    return false;
  }
  
  void check_conflict_and_propagations()
  {
    if(_conflict)
      return;
    
    for(; _pending_pos < _val.stack_size(); _pending_pos++)
      {
	literal l = _val[_pending_pos];
	literal lop = opposite_literal(l);

	std::vector<clause *> & w_lop = _watch_lists[lop];
	
	unsigned k = 0;	
	for(unsigned i = 0; i < w_lop.size(); i++)
	  {
	    unsigned p;
	    bool found_true = false;

	    if(!find_alternative_watch(w_lop[i], p))
	      {
		literal ow = lop == (*w_lop[i])[0] ? (*w_lop[i])[1] : (*w_lop[i])[0];
		extended_boolean owv = _val.literal_value(ow);

		w_lop[k++] = w_lop[i];

		if(owv == B_FALSE)
		  {
		    for(unsigned j = i + 1; j < w_lop.size(); j++)
		      w_lop[k++] = w_lop[j];
		    w_lop.resize(k);

		    _conflict = true;		    
		    return;
		  }
		else if(owv == B_UNDEFINED)
		  {
		    apply_unit_propagation(ow);
		  }
	      }
	    else
	      {
		_watch_lists[(*w_lop[i])[p]].push_back(w_lop[i]);
		if((*w_lop[i])[0] == lop)
		  std::swap((*w_lop[i])[0], (*w_lop[i])[p]);
		else
		  std::swap((*w_lop[i])[1], (*w_lop[i])[p]);
	      }
	  }
	w_lop.resize(k);	
      }
    return;
  }

  bool true_literal_exists(const clause & cl, unsigned & i)
  {
    for(i = 0; i < cl.size(); i++)
      {
	if(_val.literal_value(cl[i]) == B_TRUE)
	  return true;
      }
    return false;
  }
  
  void simplify()
  {
    for(unsigned l = 0; l < _watch_lists.size(); l++)
      {
	std::vector<clause *> & w_list = _watch_lists[l];

	unsigned k = 0;
	for(unsigned j = 0; j < w_list.size(); j++)
	  {
	    unsigned i;
	    if(!true_literal_exists(*w_list[j], i))
	      {
		w_list[k++] = w_list[j];
	      }
	    else if(l != std::max((*w_list[j])[0], (*w_list[j])[1]))
	      continue;
	    else {
		_inactive_lists[(*w_list[j])[i]].push_back(w_list[j]);
		if(i != 0)
		  std::swap((*w_list[j])[0], (*w_list[j])[i]);
	    }
	  }
	w_list.resize(k);	
      }
  }
  
  bool choose_decision_literal(literal & l)
  {
    unsigned num_of_vars = _val.num_of_vars();
    for(; _next_decision < num_of_vars; _next_decision++)
      if(_val.variable_value(_next_decision) == B_UNDEFINED)
	{
	  l = lit_from_var(_next_decision++, P_NEGATIVE);
	  return true;
	}
    return false;
  }

  bool can_backtrack()
  {
    return _val.current_level() > 0;
  }

  void apply_unit_propagation(literal l)
  {
    //std::cout << "UnitPropagate: " << int_from_lit(l) << std::endl;
    _val.push(l);
  }
  
  void apply_decide(literal l)
  {
    //std::cout << "Decide: " << int_from_lit(l) << std::endl;
    _val.push(l, true);
    //_decide_count++;
  }

  void apply_backtrack()
  {
    //std::cout << "Backtrack" << std::endl;
    literal l = _val.backtrack();    
    _val.push(opposite_literal(l));
    _pending_pos = _val.stack_size() - 1;
    _next_decision = var_from_lit(l) + 1;
    _conflict = false;
    //_backtrack_count++;
  }

  bool solve()
  {
    //_num_solve++;
    
    literal l;
    unsigned i;

    if(_next_model)
      {	
	_conflict = true;
      }

    bool simplified = true;
    while(true)
      {
	check_conflict_and_propagations();
	if(_conflict)
	  {
	    if(can_backtrack())
	      {
		apply_backtrack();
		if(_val.current_level() == 0)
		  simplified = false;
	      }
	    else
	      {		    		
		return false;
	      }
	  }
	else {
	  if(!simplified && _val.current_level() == 0)
	    {
	      simplify();
	      simplified = true;
	    }
	  
	  if(choose_decision_literal(l))
	    {
	      apply_decide(l);
	    }
	  else
	    {
	    _next_model = true;
	    
	    return true;
	    }
	}
      }
  }

  ~solver()
  {
    //    std::cout << "Avg decides: " << (double)_decide_count/_num_solve << std::endl;
    // std::cout << "Avg backtracks: " << (double)_backtrack_count / _num_solve << std::endl;
  }

};


#endif // _DPLL_H_
