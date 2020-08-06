#ifndef _BDD_SOLVER_H
#define _BDD_SOLVER_H

extern "C" {
#include "bddlib/bddlib.h"
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
  bdd_data _data;
  int _a[221];  
  obdd_t* _b[221];
  unsigned _size;
public:
  valuation(unsigned size)
  {
    _size = size;
    _data.a = _a;
    _data.b = _b;
    reset(nullptr);
  }

  
  void reset(obdd_t * p)
  {    
    for(unsigned i = 0; i <= _size; i++)
      {
	_a[i] = 0;
	_b[i] = nullptr;
      }
    _data.n = _size;
    _data.s = 0;
    _data.t = 0;
    _data.done = 0;
    _data.sol_found = 0;
    _data.p = p;
    _data.first_time = 1;
  }

  bool get_next_solution()
  {
    if(_data.done == 0)
      {
	decompose_bdd(&_data);
	return _data.sol_found == 1;
      }
    else
      return false;
  }
  
  extended_boolean variable_value(variable v) const
  {
    return _a[v] > 0 ? B_TRUE : B_FALSE;
  }
  
  void print(std::ostream & ostr) const
  {
    for(unsigned i = 0; i < _size; i++)
      ostr << (variable_value(i) == B_TRUE ? int_from_lit(lit_from_var(i, P_POSITIVE)) : int_from_lit(lit_from_var(i, P_NEGATIVE))) << " ";
    ostr << "0" << std::endl;
  }
  
};


class solver {
private:
  bddsolver * _s = nullptr;
  valuation _val;
  unsigned _num_of_vars;
  bool _conflict = false;
public:
  solver(unsigned num)
    :_val(num),
     _num_of_vars(num)
  {}

  bool solve()
  {
    if(_conflict)
      return false;

    return _val.get_next_solution();
    
  }

  const valuation & val()
  {
    return _val;
  }

  bool solver_created()
  {
    return _s != nullptr;
  }
  
  void reset_solver()
  {
    if(_s != nullptr)
      {
	release_obdd_storage(0);	
	solver_reset(_s);
      }
    else
      _s = solver_new();
    _conflict = false;
  }
  
  void add_clauses(const std::vector<clause> & clauses, bool persistent)
  {
      
    for(unsigned i = 0; i < clauses.size(); i++)      
      {
       	const clause & cl = clauses[i];
	
	int data[13];
	for(unsigned k = 0; k < cl.size(); k++)
	  data[k] = cl[k];
	
	bool retval = (bool) solver_addclause(_s, data, data + cl.size());
	if(retval == false)
	  {
	    _conflict = true;
	    return;
	  }
      }

    if(persistent && solver_npersistent(_s) == 0)
      solver_setpersistent(_s);	  	
  }

  void initialize_solver()
  {
    if(solver_simplify(_s)  == -1)
      _conflict = true;
    else
      {
	solver_solve(_s,0,0);
	_val.reset(get_root(_s));
      }
  }
  
  ~solver() {
    if(_s != nullptr)
      {
	solver_delete(_s);
	release_obdd_storage(1);
      }
  }
  
};

#endif // _BDD_SOLVER_H
