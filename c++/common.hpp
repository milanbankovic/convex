#include <cassert>
#include <iostream>
#include <iomanip>
#include <vector>
#include <utility>
#include <functional>
#include <algorithm>
#include <string>
#include <fstream>
#include <unordered_map>
#include <unordered_set>
#include <numeric>
#include <memory>


#ifdef BDD_CONVEX
#include "bddsolver.hpp"
#elif defined PICO_CONVEX
#include "picosolver.hpp"
#else
#include "dpll.hpp"
#endif

#ifdef _PARALLEL
#define TBB_SUPPRESS_DEPRECATED_MESSAGES 1
#include <tbb/tbb.h>
#endif


using permutation = std::vector<unsigned>;

namespace std {

  template <>
  struct hash<permutation> {
    std::size_t operator () (const permutation & perm) const
    {
      return std::accumulate(perm.begin(), perm.end(), 0, [] (std::size_t init, unsigned next) -> std::size_t
							  {
							    return init * 157 + next;
							  });
    }
  };
}

void print_permutation(std::ostream & ostr, const permutation & perm)
{
  ostr << "( ";
  for(auto x : perm)
    ostr << x << " ";
  ostr << ")" << std::endl;
}


#if defined _USE_SHARED_PTR && !defined _PARALLEL

/* For efficiency reasons, vectors of automorphisms of each
   configuration will contain pointers to permutations instead of the
   permutations.  Each permutation will be stored in exactly one place
   in the memory, and it will be referenced where needed by using
   shared pointers. */
using permutation_ptr = std::shared_ptr<const permutation>;


// Singleton class that is responsible for menagement of the
// permutations and their shared pointers
class permutation_memory {
private:
  using weak_perm_ptr = std::weak_ptr<const permutation>;
  std::unordered_map<permutation, weak_perm_ptr> _perm_map;
  
  struct deleter {
    permutation_memory * _memory;

    deleter(permutation_memory * memory)
      :_memory(memory)
    {}
    
    void operator () (const permutation * perm)
    {
      _memory->_perm_map.erase(*perm);
    }
    
  };
  static permutation_memory * _memory;

  permutation_memory() {}
  
public:

  static permutation_memory * get_instance()
  {
    if(_memory == nullptr)
      _memory = new permutation_memory();
    return _memory;      
  }

  static void delete_instance()
  {
    delete _memory;
  }

  permutation_ptr get_shared_ptr(const permutation & perm)
  {
    permutation_ptr ptr;
    
    auto it = _perm_map.find(perm);
    if(it == _perm_map.end())
      {
	it = _perm_map.insert(std::make_pair(perm, weak_perm_ptr())).first;
	it->second = weak_perm_ptr(ptr = permutation_ptr(&it->first, deleter(this)));	
      }
    else
      {
	ptr = permutation_ptr(it->second);
      }
    
    return ptr;
  }  
};

permutation_memory * permutation_memory::_memory = nullptr;

// Shared pointer wrapper for permutations
inline
permutation_ptr get_perm_ptr(const permutation & perm)
{
  return permutation_memory::get_instance()->get_shared_ptr(perm);
}

#else

using permutation_ptr = permutation;

inline
const permutation_ptr & get_perm_ptr(const permutation & perm)
{
  return perm;
}

inline
const permutation & operator * (const permutation_ptr & ptr)
{
  return ptr;
}

#endif


// Generates initial permutation {0, 1, 2, ..., size -1 }
void initial_permutation(permutation & perm, unsigned size)
{
  //perm.clear();
  perm.resize(size);
  for(unsigned i = 0; i < size; i++)
    perm[i] = i;
}


#ifdef _ORDER_TYPES
// Generate mirrored initial permutation { size - 1, size - 2, ..., 2, 1, 0 }
void mirrored_initial_permutation(permutation & perm, unsigned size)
{
  perm.resize(size);
  for(unsigned i = 0; i < size; i++)
    perm[i] = size - 1 - i;
}
#endif


// Triplet of points <p,q,r>
using triplet = std::tuple<unsigned, unsigned, unsigned>;

inline
std::ostream & operator << (std::ostream & ostr, const triplet & tr)
{
  ostr << "(" << std::get<0>(tr) << "," << std::get<1>(tr) << "," << std::get<2>(tr) << ")";
  return ostr;
}

// Next triplet (<0,1,2>, <0,1,3>, <0,2,3>, <1,2,3>, <0,1,4>, <0,2,4>,
// <1, 2, 4>, <0, 3, 4>, <1, 3, 4>, <2, 3, 4> ...)
inline
void next_triplet(triplet & tr)
{
  if(std::get<0>(tr) + 1 < std::get<1>(tr))
    {
      std::get<0>(tr)++;
    }
  else if(std::get<1>(tr) + 1 < std::get<2>(tr))
    {
      std::get<1>(tr)++;
      std::get<0>(tr) = 0;
    }
  else
    {
      std::get<2>(tr)++;
      std::get<0>(tr) = 0;
      std::get<1>(tr) = 1;
    }
}

// Number of (ascending) triplets of 'size' points
inline
int num_of_triplets(unsigned size)
{
  return size * (size - 1) * (size - 2) / 6;
}

// Is triplet positively oriented (i.e. i < j < k modulo rotation)
inline
bool triplet_positive(const triplet & tr)
{
  return (std::get<0>(tr) < std::get<1>(tr) &&
	  std::get<1>(tr) < std::get<2>(tr)) ||
			    (std::get<1>(tr) < std::get<2>(tr) &&
			     std::get<2>(tr) < std::get<0>(tr)) ||
					       (std::get<2>(tr) < std::get<0>(tr) &&
						std::get<0>(tr) < std::get<1>(tr));
}

// Sort triplet in ascending order
inline
void normalize_triplet(triplet & tr)
{
  if(std::get<0>(tr) > std::get<1>(tr))
    std::swap(std::get<0>(tr), std::get<1>(tr));
  if(std::get<1>(tr) > std::get<2>(tr))
    std::swap(std::get<1>(tr), std::get<2>(tr));
  if(std::get<0>(tr) > std::get<1>(tr))
    std::swap(std::get<0>(tr), std::get<1>(tr));
}

// Calculates the position of a triplet in configurations
inline
unsigned triplet_position(const triplet & tr)
{
  unsigned i = std::get<0>(tr);
  unsigned j = std::get<1>(tr);
  unsigned k = std::get<2>(tr);
  return num_of_triplets(k) + (j*(j-1) >> 1) + i;
}

// Configuration (for instance -|-+-|+++--+)
using configuration = std::vector<bool>;

std::ostream & operator << (std::ostream & ostr, const configuration & conf)
{
  unsigned next_boundary = 1;
  unsigned current_size = 3;
  for(unsigned i = 0; i < conf.size(); i++)
    {
      if(i == next_boundary)
	{
	  current_size++;
	  next_boundary = num_of_triplets(current_size);
	  ostr << "|";
	}
      ostr << (conf[i] ? "+" : "-");
    }
  return ostr;
}

// Convex hulls structure of a configuration (for instance [5,4,1])
using structure = std::vector<int>;

std::ostream & operator << (std::ostream & ostr, const structure & str)
{
  ostr << "[ ";
  for(unsigned i = 0; i < str.size(); i++)
    {
      ostr << str[i] << " ";     
    }
  ostr << "]";
  return ostr;
}


/* Incrementally builds the permutation that could produce a smaller
   configuration than conf.  The procedure is recursive, and parametar
   k tells us how many values are fixed so far by the partial
   permutation (perm[0],...,perm[k-1]). perm[k],...,perm[n-1] are the
   unused values that could be used to extend the current partial
   permutation. Initially, it is invoked with perm equal to some
   automorphism of the previous structure, and with k equal to the
   index of the first point in the innermost hull (since we are
   permuting only the innermost hull). In new_perm the automorphisms
   of the configuration are stored. */
#ifdef _ORDER_TYPES
bool search_smaller_permutation(permutation & perm,
				unsigned k,
				const configuration & conf,
				std::vector<permutation_ptr> & new_perms,
				bool mirrored = false)
#else
  bool search_smaller_permutation(permutation & perm,
				  unsigned k,
				  const configuration & conf,
				  std::vector<permutation_ptr> & new_perms)
#endif
{
#ifndef _PARALLEL
  static std::vector<std::vector<unsigned>> equals(13);
#else
  static tbb::combinable<std::vector<std::vector<unsigned>>> equals_comb([](){ return std::vector<std::vector<unsigned>>(13); });
  std::vector<std::vector<unsigned>> & equals = equals_comb.local();
#endif
  
  unsigned size = perm.size();
  equals[k].clear();
  
  /* Checking the possible values to assign to k in order to extend
     the partial permutation perm[0],perm[1],...,perm[k-1].  */
  for(unsigned i = k; i < size; i++)
    {
      // Trying the value perm[i]
      std::swap(perm[i], perm[k]);
      bool rec = true;
      
      // for k = 0, 1, all the values can be assigned, since no
      // triplets are still determined
      if(k >= 2)
	{
	  triplet tr = triplet { 0, 1, k };
	  unsigned num_of_tr = num_of_triplets(k + 1);

	  // finding the prefix of the transformed configuration
	  for(unsigned j = num_of_triplets(k); j < num_of_tr; j++)
	    {
	      triplet trans_tr = triplet { perm[std::get<0>(tr)], perm[std::get<1>(tr)], perm[std::get<2>(tr)] };
	      bool positive = triplet_positive(trans_tr);
	      normalize_triplet(trans_tr);
	      unsigned tr_pos = triplet_position(trans_tr);
#ifdef _ORDER_TYPES
	      bool new_conf = positive && !mirrored || !positive && mirrored ? conf[tr_pos] : !conf[tr_pos];
#else
	      bool new_conf = positive ? conf[tr_pos] : !conf[tr_pos];
#endif
	      if(!new_conf && conf[j])
		{
		  return true;  // FOUND SMALLER CONFIGURATION
		}
	      else if(new_conf && !conf[j])
		{
		  rec = false;  // GREATER CONFIGURATION, SKIP IT
		  break;
		}
	      next_triplet(tr);	      
	    }	  
	}

      // If configuration is not skipped, it means that the prefixes coincide, so we push it to
      // the equals array in order to try it later in the recursive call (only permutations that
      // produce equal prefixes are further checked in recursive fashion)
      if(rec)
	equals[k].push_back(i);
	  
      std::swap(perm[i], perm[k]);            
    }

  // If we have a complete permutation ...
  if(k + 1 == size)
    {
      assert(perm.size() == size);
      if(!equals[k].empty()) // if it is an authomorphism...
	{
	  assert( std::find(new_perms.begin(), new_perms.end(), get_perm_ptr(perm)) == new_perms.end() );
	  new_perms.push_back(get_perm_ptr(perm));
	}
      return false;
    }

  // Try to extend the partial permutation with the values that produce equal prefixes, and check
  // them recursively. 
  for(unsigned i = 0; i < equals[k].size(); i++)
    {
      std::swap(perm[equals[k][i]], perm[k]);

#ifdef _ORDER_TYPES
      if(search_smaller_permutation(perm, k + 1, conf, new_perms, mirrored))
#else
	if(search_smaller_permutation(perm, k + 1, conf, new_perms))
#endif
	return true; 
	  
      std::swap(perm[equals[k][i]], perm[k]);
    }
    
  return false;
}


class cyclic_store {
private:
  std::vector<std::vector<permutation_ptr>> _cyclic_permutations;
#ifdef _ORDER_TYPES
  std::vector<std::vector<permutation_ptr>> _mirrored_cyclic_permutations;
#endif
  
  void init_cyclic_permutations(unsigned size)
  {
    std::vector<permutation_ptr> & retval = _cyclic_permutations[size];
#ifdef _ORDER_TYPES
    std::vector<permutation_ptr> & m_retval = _mirrored_cyclic_permutations[size];
#endif
    
    if(!retval.empty())
      return;
  
    permutation perm;
    initial_permutation(perm, size);
    retval.push_back(get_perm_ptr(perm));
#ifdef _ORDER_TYPES
    mirrored_initial_permutation(perm, size);
    m_retval.push_back(get_perm_ptr(perm));
#endif
    
    if(size == 0)
      return;
  
    for(unsigned i = 0; i < size - 1; i++)
      {
	perm = *retval.back();
	std::rotate(perm.begin(), std::next(perm.begin()), perm.end());
	retval.push_back(get_perm_ptr(perm));
#ifdef _ORDER_TYPES
	perm = *m_retval.back();
	std::rotate(perm.begin(), std::next(perm.begin()), perm.end());
	m_retval.push_back(get_perm_ptr(perm));
#endif	
      }
  }

  cyclic_store(unsigned limit_size)
    :_cyclic_permutations(limit_size + 1)
#ifdef _ORDER_TYPES
    ,_mirrored_cyclic_permutations(limit_size + 1)
#endif
  {
    for(unsigned i = 0; i <= limit_size; i++)
      init_cyclic_permutations(i);
  }

  static cyclic_store * _instance;
  
public:
  const std::vector<permutation_ptr> & cyclic_permutations(unsigned size) const
  {
    return _cyclic_permutations[size];
  }

#ifdef _ORDER_TYPES
  const std::vector<permutation_ptr> & mirrored_cyclic_permutations(unsigned size) const
  {
    return _mirrored_cyclic_permutations[size];
  }  
#endif
  
  static void init_instance(unsigned limit_size)
  {
    if(_instance == nullptr)
      _instance = new cyclic_store(limit_size);

  }
  
  static const cyclic_store * get_instance()
  {
    return _instance;
  }

  static void delete_instance()
  {
    delete _instance;
    _instance = nullptr;
  }
  
};

cyclic_store * cyclic_store::_instance = nullptr;

inline
const std::vector<permutation_ptr> & cyclic_permutations(unsigned size)
{
  return cyclic_store::get_instance()->cyclic_permutations(size);
}

#ifdef _ORDER_TYPES
inline
const std::vector<permutation_ptr> & mirrored_cyclic_permutations(unsigned size)
{
  return cyclic_store::get_instance()->mirrored_cyclic_permutations(size);
}
#endif

class smallest_configurations {
private:
  std::vector<configuration> _smallest;

  smallest_configurations(unsigned limit_size)
    :_smallest(limit_size + 1)
  {
    for(unsigned i = 0; i <= limit_size; i++)
      _smallest[i] = configuration(num_of_triplets(i), false);
  }

  static smallest_configurations * _instance;
public:

  const configuration & smallest_configuration(unsigned size)
  {
    return _smallest[size];
  }

  static void init_instance(unsigned limit_size)
  {
    if(_instance == nullptr)
      _instance = new smallest_configurations(limit_size);
  }

  static smallest_configurations * get_instance()
  {
    return _instance;
  }

  static void delete_instance()
  {
    delete _instance;
    _instance = nullptr;
  }
  
};
smallest_configurations * smallest_configurations::_instance = nullptr;

const configuration & smallest_configuration(unsigned size)
{
  return smallest_configurations::get_instance()->smallest_configuration(size);
}



// Checks if the configuration is canonical (i.e. smallest of all in its class)
inline
bool is_canonical(const configuration & conf,
		  unsigned struct_size, 
		  const std::vector<permutation_ptr> & prev_perms,
#ifdef _ORDER_TYPES
		  const std::vector<permutation_ptr> & m_prev_perms,
#endif
		  unsigned size,
		  std::vector<permutation_ptr> & new_perms
#ifdef _ORDER_TYPES
		  , std::vector<permutation_ptr> & m_new_perms
#endif
		  )
{
  // Special case: convex poligon -- only all-false configuration is
  // canonical
  if(struct_size == 1)
    {
      if(conf != smallest_configuration(size))
	return false;
      else
	{
	  new_perms = cyclic_permutations(size);
#ifdef _ORDER_TYPES
	  m_new_perms = mirrored_cyclic_permutations(size);
#endif
	  return true;
	}
    }

  permutation perm;
  // Special case: previous structure has only trivial automorhism,
  // and only one point is in the last hull
#ifdef _ORDER_TYPES
  if(m_prev_perms.size() == 0 && prev_perms.size() == 1 && (*prev_perms[0]).size() == size - 1)
#else
    if(prev_perms.size() == 1 && (*prev_perms[0]).size() == size - 1)
#endif
    {
      perm = *prev_perms[0];
      perm.push_back(size - 1);
      new_perms.push_back(get_perm_ptr(perm));
      return true;
    }

  // General case: for all authomorphisms of the previous structure...
  for(const auto & prev_perm : prev_perms)
    {
      perm = *prev_perm;

      unsigned k = perm.size();
      for(unsigned t = k; t < size; t++)
	perm.push_back(t);
      
      if(search_smaller_permutation(perm, k, conf, new_perms))
	{
	  return false;
	}
    }

#ifdef _ORDER_TYPES
  // General case: for all authomorphisms of the previous structure...
  for(const auto & m_prev_perm : m_prev_perms)
    {
      perm = *m_prev_perm;

      unsigned k = perm.size();
      for(unsigned t = k; t < size; t++)
	perm.push_back(t);
      
      if(search_smaller_permutation(perm, k, conf, m_new_perms, true))
	{
	  return false;
	}
    }  
#endif
  
  return true;
}



class configuration_generator {
private:
  unsigned _size;
  std::vector<clause> _axiom_clauses;
  std::vector<clause> _prev_conf_clauses;
  std::vector<clause> _prev_struct_clauses;
  std::vector<clause> _new_struct_clauses;
  solver _s;
  bool _first_conf;
public:
  configuration_generator(unsigned size)
    :_size(size),
     _s(num_of_triplets(size)),
     _first_conf(true)
  {
    
    if(size < 4)
      return;
    
    // Axiom 4
    triplet qr = triplet { 0, 1, 2 };
    unsigned num_of_tr = num_of_triplets(size-1);
    unsigned t = size - 1;
    
    for(unsigned i = 0; i < num_of_tr; i++)
      {      
	unsigned qrt_pos = triplet_position(triplet { std::get<1>(qr), std::get<2>(qr), t });
	unsigned prt_pos = triplet_position(triplet { std::get<0>(qr), std::get<2>(qr), t });
	unsigned pqt_pos = triplet_position(triplet { std::get<0>(qr), std::get<1>(qr), t });
	unsigned pqr_pos = triplet_position(triplet { std::get<0>(qr), std::get<1>(qr), std::get<2>(qr) });

	
	_axiom_clauses.push_back({ lit_from_var(qrt_pos, P_NEGATIVE),
				   lit_from_var(prt_pos, P_POSITIVE),
				   lit_from_var(pqt_pos, P_NEGATIVE),
				   lit_from_var(pqr_pos, P_POSITIVE) });

	_axiom_clauses.push_back({ lit_from_var(qrt_pos, P_POSITIVE),
				   lit_from_var(prt_pos, P_NEGATIVE),
				   lit_from_var(pqt_pos, P_POSITIVE),
				   lit_from_var(pqr_pos, P_NEGATIVE) });
	
	next_triplet(qr);
      }
    
    if(size < 5)
      return;
    
    // Axiom 5
    triplet tr = triplet { 0, 1, 2 };
    num_of_tr = num_of_triplets(size);
  
    for(unsigned i = 0; i < num_of_tr; i++)
      {
	for(unsigned t = 0; t < size; t++)
	  {
	    if(t == std::get<0>(tr) || t == std::get<1>(tr) || t == std::get<2>(tr))
	      continue;
	    	      	  
	    for(unsigned s = (std::get<2>(tr) != size - 1 && t != size - 1) ? size - 1 : 0; s < size; s++)
	      {
		if(s == std::get<0>(tr) || s == std::get<1>(tr) || s == std::get<2>(tr) || s == t)
		  continue;	    
	    
		triplet pts = triplet {std::get<0>(tr), t, s};
		triplet qts = triplet {std::get<1>(tr), t, s};
		triplet rts = triplet {std::get<2>(tr), t, s};
		triplet pqt = triplet {std::get<0>(tr), std::get<1>(tr), t};
		triplet qrt = triplet {std::get<1>(tr), std::get<2>(tr), t};
		triplet prt = triplet {std::get<0>(tr), std::get<2>(tr), t};

		bool pts_pol = triplet_positive(pts);
		bool qts_pol = triplet_positive(qts);
		bool rts_pol = triplet_positive(rts);
		bool pqt_pol = triplet_positive(pqt);
		bool qrt_pol = triplet_positive(qrt);
		bool prt_pol = triplet_positive(prt);

		normalize_triplet(pts);
		normalize_triplet(qts);
		normalize_triplet(rts);
		normalize_triplet(pqt);
		normalize_triplet(qrt);
		normalize_triplet(prt);
	    
		unsigned pts_pos = triplet_position(pts);
		unsigned qts_pos = triplet_position(qts);
		unsigned rts_pos = triplet_position(rts);
		unsigned pqt_pos = triplet_position(pqt);
		unsigned qrt_pos = triplet_position(qrt);
		unsigned prt_pos = triplet_position(prt);


		_axiom_clauses.push_back( { lit_from_var(pts_pos, pts_pol ? P_NEGATIVE : P_POSITIVE),
					    lit_from_var(qts_pos, qts_pol ? P_NEGATIVE : P_POSITIVE),
					    lit_from_var(rts_pos, rts_pol ? P_NEGATIVE : P_POSITIVE),
					    lit_from_var(pqt_pos, pqt_pol ? P_NEGATIVE : P_POSITIVE),
					    lit_from_var(qrt_pos, qrt_pol ? P_NEGATIVE : P_POSITIVE),
					    lit_from_var(prt_pos, prt_pol ? P_POSITIVE : P_NEGATIVE) });
		
		_axiom_clauses.push_back( { lit_from_var(pts_pos, pts_pol ? P_NEGATIVE : P_POSITIVE),
					    lit_from_var(qts_pos, qts_pol ? P_NEGATIVE : P_POSITIVE),
					    lit_from_var(rts_pos, rts_pol ? P_NEGATIVE : P_POSITIVE),
					    lit_from_var(pqt_pos, pqt_pol ? P_POSITIVE : P_NEGATIVE),
					    lit_from_var(qrt_pos, qrt_pol ? P_POSITIVE : P_NEGATIVE),
					    lit_from_var(prt_pos, prt_pol ? P_NEGATIVE : P_POSITIVE) });
	      }
	  }
	
	next_triplet(tr);
      }
#ifndef BDD_CONVEX 
    _s.add_clauses(_axiom_clauses);
#endif
  }
  
  void set_configuration(const configuration & old_conf, const structure & prev_struct)
  {
    //    std::cout << "ENTER SET_CONFIGURATION" << std::endl;
#ifndef BDD_CONVEX
    _s.restore_clause_context(0);    
#endif
    _prev_conf_clauses.clear();
    _prev_struct_clauses.clear();
    
    // Unit clauses that fix old configuration that is being augmented
    for(unsigned v = 0; v < old_conf.size(); v++)
      {
	_prev_conf_clauses.push_back({ lit_from_var(v, old_conf[v] ? P_POSITIVE : P_NEGATIVE) });
      }

    unsigned s = 0;  // Start point of the current hull

    for(unsigned i = 0, limit = prev_struct.size() - 1; i < limit; i++)
      {
	std::vector<unsigned> hull(prev_struct[i]);
	for(unsigned j = 0; j < hull.size(); j++)
	  {
	    hull[j] = s + j;
	    assert(hull[j] != _size - 1);
	  }
	std::sort(hull.begin() + 1, hull.end(), [&old_conf, s] (unsigned x, unsigned y) -> bool
						{
						  triplet tr {s, x, y};
						  bool tr_pol = triplet_positive(tr);
						  normalize_triplet(tr);
						  unsigned tr_pos = triplet_position(tr);
						  return tr_pol ? old_conf[tr_pos] : !old_conf[tr_pos]; 
						});      	

	for(unsigned j = 0; j < hull.size(); j++)
	  {
	    triplet tr { hull[j], hull[j+1 < hull.size() ? j+1 : 0], _size - 1 };		
	    bool tr_pol = triplet_positive(tr);
	    normalize_triplet(tr);
	    unsigned tr_pos = triplet_position(tr);
	    _prev_struct_clauses.push_back( { lit_from_var(tr_pos, tr_pol ? P_POSITIVE : P_NEGATIVE) });
	  }	
	s += hull.size();
      }
#ifndef BDD_CONVEX
    _s.add_clause_context();
    _s.add_clauses(_prev_conf_clauses);
    _s.add_clauses(_prev_struct_clauses);
#endif
  }

  void set_structure(const configuration & old_conf, const structure & str)
  {
    //    std::cout << "ENTER SET_STRUCTURE: " << old_conf << ", " << str << " (" << _size << ")" << std::endl;
#ifndef BDD_CONVEX
    _s.restore_clause_context(1);
#endif
    _new_struct_clauses.clear();
    
    unsigned s;
    if(str.back() == 1)      
      s = _size - 1 - str[str.size() - 2];
    else
      s = _size - str.back();

    unsigned hull_size = _size - s - 1;
    
    if(hull_size >= 3)
      {	
	std::vector<unsigned> hull(hull_size);
	
	for(unsigned j = 0; j < hull_size; j++)
	  {
	    hull[j] = s + j;
	    assert(hull[j] != _size - 1);
	  }
       	
	std::sort(hull.begin() + 1, hull.end(), [&old_conf, s] (unsigned x, unsigned y) -> bool
						{
						  triplet tr {s, x, y};
						  bool tr_pol = triplet_positive(tr);
						  normalize_triplet(tr);
						  unsigned tr_pos = triplet_position(tr);
						  return tr_pol ? old_conf[tr_pos] : !old_conf[tr_pos]; 
						});
	
	if(str.back() == 1)
	  {
	    for(unsigned j = 0; j < hull.size(); j++)
	      {
		triplet tr { hull[j], hull[j+1 < hull.size() ? j+1 : 0], _size - 1 };		
		bool tr_pol = triplet_positive(tr);
		normalize_triplet(tr);
		unsigned tr_pos = triplet_position(tr);
		_new_struct_clauses.push_back( { lit_from_var(tr_pos, tr_pol ? P_POSITIVE : P_NEGATIVE) });
	      }	
	  }
	else
	  {      
	    clause cl;
	    for(unsigned j = 0; j < hull.size(); j++)
	      {
		triplet tr { hull[j], hull[j+1 < hull.size() ? j+1 : 0], _size - 1 };
		bool tr_pol = triplet_positive(tr);
		normalize_triplet(tr);
		unsigned tr_pos = triplet_position(tr);
		cl.push_back(lit_from_var(tr_pos, tr_pol ? P_NEGATIVE : P_POSITIVE));		
	      }
	    _new_struct_clauses.push_back(cl);
	    for(unsigned j1 = 0; j1 < cl.size(); j1++)
	      for(unsigned j2 = j1 + 1; j2 < cl.size(); j2++)
		{
		  _new_struct_clauses.push_back({ opposite_literal(cl[j1]), opposite_literal(cl[j2]) });
		}
	  }
      }
    _first_conf = true;
    
#ifndef BDD_CONVEX
    _s.add_clause_context();
    _s.add_clauses(_new_struct_clauses);
#else
    if(!_s.solver_created())
      {
	_s.reset_solver();
	_s.add_clauses(_axiom_clauses, true);
      }
    else
      _s.reset_solver();
    _s.add_clauses(_prev_conf_clauses, false);
    _s.add_clauses(_prev_struct_clauses, false);
    _s.add_clauses(_new_struct_clauses, false);
    _s.initialize_solver();
#endif

#if !defined PICO_CONVEX && !defined BDD_CONVEX
    _s.initialize_solver();
    _s.set_units();
    _s.set_watch_lists();
    _s.simplify_clauses();
#endif
  }
  
  bool generate_next_configuration(configuration & conf)
  {
    if(!_s.solve())
      return false;
    
    unsigned conf_size = conf.size();
    for(unsigned v = _first_conf ? 0 : num_of_triplets(_size - 1) ; v < conf_size; v++)
      {	
	conf[v] = _s.val().variable_value(v) == B_TRUE ? true : false;
      }
    
    _first_conf = false;
    return true;
  }
};

