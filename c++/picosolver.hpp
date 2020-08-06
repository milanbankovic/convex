#ifndef _PICOSOLVER_H
#define _PICOSOLVER_H

extern "C" {
#include "picosat/picosat.h"
}

#include <vector>
#include <cstdlib>

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


enum extended_boolean {
  B_FALSE = -1,
  B_UNDEFINED = 0,
  B_TRUE = 1
};

typedef std::vector<literal> clause;


class valuation {
private:
  std::vector<extended_boolean> _values;
public:
  valuation(unsigned size)
    :_values(size, B_UNDEFINED)
  {}

  extended_boolean variable_value(variable v) const
  {
    return _values[v];
  }

  void set_variable_value(variable v, extended_boolean b)
  {
    _values[v] = b;
  }
  
  void print(std::ostream & ostr) const
  {
    for(unsigned i = 0; i < _values.size(); i++)
      ostr << (variable_value(i) == B_TRUE ? int_from_lit(lit_from_var(i, P_POSITIVE)) : int_from_lit(lit_from_var(i, P_NEGATIVE))) << " ";
    ostr << "0" << std::endl;
  }

};

class unit_stack {
private:
  std::vector<bool> _units;
  std::vector<variable> _stack;
  std::vector<unsigned> _stack_levels;
public:
  unit_stack(unsigned size)
    :_units(size, false)
  {}

  bool is_unit(variable v) const
  {
    return _units[v];
  }
  
  void push_unit_variable(variable v)
  {
    _stack.push_back(v);
    _units[v] = true;
  }

  void new_level()
  {
    _stack_levels.push_back(_stack.size());
  }
  
  void restore_level(unsigned k)
  {
    if(k >= _stack_levels.size())
      return;
    
    while(_stack.size() > _stack_levels[k])
      {
	_units[_stack.back()] = false;
	_stack.pop_back();
      }
    _stack_levels.resize(k);    
  }

  void clear()
  {
    _units.assign(_units.size(), false);
    _stack.clear();
    _stack_levels.clear();
  }
};

class solver {
private:
  valuation _val;
  PicoSAT * _picosat = nullptr;
  unsigned _num_of_vars;
  unsigned _num_of_contexts;
  unit_stack _unit_stack;
public:
  solver(unsigned num)
    :_val(num),
     _num_of_vars(num),
     _num_of_contexts(0),
     _unit_stack(num)
  {
    initialize_solver();
  }

  bool solve()
  {
    picosat_set_seed(_picosat, 0);
    int res = picosat_sat (_picosat, -1);
    
    if(res == PICOSAT_SATISFIABLE)
      {
	for(unsigned v = 0; v < _num_of_vars; v++)
	  {
	    int ret = picosat_deref(_picosat, v+1);
	    _val.set_variable_value(v, (extended_boolean) ret);
	  }
		
	for(unsigned v = 0; v < _num_of_vars; v++)
	  {
	    if(!_unit_stack.is_unit(v))	    
	      picosat_add(_picosat, _val.variable_value(v) == B_TRUE ? -(v+1) : (v+1));
	  }
	picosat_add(_picosat, 0);
	
	return true;
      }
    return false;
  }

  const valuation & val()
  {
    return _val;
  }

  void initialize_solver()
  {
    _num_of_contexts = 0;
    if(_picosat != nullptr)
      picosat_reset(_picosat);
    
    _picosat = picosat_init();
    picosat_set_verbosity(_picosat, 0);
    picosat_set_plain(_picosat, 1);
    picosat_set_global_default_phase(_picosat, 0);
    picosat_adjust(_picosat, _num_of_vars);
    
    _unit_stack.clear();
  }
  
  void add_clause_context()
  {
    picosat_push(_picosat);
    _num_of_contexts++;
    _unit_stack.new_level();
  }
  
  void add_clauses(const std::vector<clause> & clauses)
  {
    for(unsigned k = 0; k < clauses.size(); k++)
      {
	const clause & cl = clauses[k];

	if(cl.size() == 1)
	  _unit_stack.push_unit_variable(var_from_lit(cl[0]));
	
	for(unsigned i = 0; i < cl.size(); i++)
	  {
	    picosat_add(_picosat, int_from_lit(cl[i]));
	  }
	picosat_add(_picosat, 0);
      }
  }

  void restore_clause_context(unsigned k)
  {
    while(_num_of_contexts > k)
      {
	picosat_pop(_picosat);	
	_num_of_contexts--;
      }
    _unit_stack.restore_level(k);
  }
  
  ~solver()
  {
    picosat_reset(_picosat);
  }
  
};


#endif // _PICOSOLVER_H
