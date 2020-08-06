#include "common.hpp"

#define NO_CHILD (unsigned (-1))

struct struct_node {
  structure _struct;
  unsigned _first_child;
  unsigned _second_child;  
};


struct conf_data {
  configuration _conf;
  unsigned _struct_index;
  std::vector<permutation_ptr> _eq_perms_p;
  std::vector<permutation_ptr> _eq_perms;
};


// An instance of Read's algorithm for enumeration of non-isomophic configurations
void enumerate_configurations(unsigned limit_size)
{
  assert(limit_size >= 3);

  // Vector of conf_data (for n and n+1 respectively). Each conf_data
  // consists of a configuration _conf, the index _struct_index of its
  // structure in the vector of structures, the vector _eq_perms of
  // the automorphisms of the configuration _conf, and the vector
  // _eq_perms_p of the automorphisms of the configuration which is
  // obtained from _conf by removing its innermost hull (denoted as
  // "previous automorphisms" in further text)
  std::vector<conf_data> prev_configs;
  std::vector<conf_data> new_configs;
  
  // Vectors of structures (for n and n+1, respectively). Each
  // struct_node in the vector of structures for n is a triplet that
  // consists of a structure and the indices of its augmented
  // structures in the vector of structures for n+1. These indices
  // are calculated lazily.
  std::vector<struct_node> prev_structs;
  std::vector<struct_node> new_structs;
  
  std::vector<permutation_ptr> new_perms;
  
  // For n=3, we have only one structure [3] (with index 0 in the
  // structs vector), and only one configuration "-" of that structure
  // The automorphisms of this configuration are all cyclic
  // permutations, and there are no previous automorphisms, since
  // there are no outher hulls.
  new_structs.push_back(struct_node { structure { 3 }, NO_CHILD, NO_CHILD });
  new_configs.push_back(conf_data { { false }, 0, {}, cyclic_permutations(3) });


#ifdef PRINT
  std::vector<conf_data> temp_configs[2];
#endif
  
  std::vector<unsigned> s_indices;
  
#ifdef PRINT
  std::cout << "1: -" << std::endl;
#endif
  
  for(unsigned size = 4; size <= limit_size; size++)
    {
      //  std::cout << "SIZE: " << size << " : " << num_of_triplets(size) << std::endl;
      prev_configs.swap(new_configs);
      prev_structs.swap(new_structs);
      new_configs.clear();
      new_structs.clear();
      
      unsigned long count_configs = 0;
      
      configuration_generator conf_gen(size);
            
      configuration new_config = smallest_configuration(size);
	        
      for(unsigned long i = 0; i < prev_configs.size(); i++)
	{	 
	  const configuration & prev_config = prev_configs[i]._conf;
	  const std::vector<permutation_ptr> & prev_perms  = prev_configs[i]._eq_perms;
	  const std::vector<permutation_ptr> & prev_perms_p = prev_configs[i]._eq_perms_p;
	  struct_node & prev_struct_node = prev_structs[prev_configs[i]._struct_index];
	  const structure & prev_struct = prev_struct_node._struct;
	  unsigned long c_conf = count_configs;

	  s_indices.clear();
	  
	  // Calculation of augmented structures
	  if(prev_struct_node._first_child == NO_CHILD)
	    {	      	  
	      structure augmented_struct = prev_struct;
	      augmented_struct.back()++;
	      new_structs.push_back(struct_node { augmented_struct, NO_CHILD, NO_CHILD });
	      prev_struct_node._first_child = new_structs.size() - 1;
	      s_indices.push_back(new_structs.size() - 1);
	      if(prev_struct.back() >= 3)
		{
		  augmented_struct.back()--;
		  augmented_struct.push_back(1);
		  new_structs.push_back(struct_node { augmented_struct, NO_CHILD, NO_CHILD });
		  prev_struct_node._second_child = new_structs.size() - 1;
		  s_indices.push_back(new_structs.size() - 1);
		}	  	  
	    }
	  else
	    {
	      s_indices.push_back(prev_struct_node._first_child);
	      if(prev_struct_node._second_child != NO_CHILD)
		{
		  s_indices.push_back(prev_struct_node._second_child);
		}	      
	    }

#ifdef PRINT
	  temp_configs[0].clear();
	  temp_configs[1].clear();
#endif
	  
	  //std::cout << "Conf: " << prev_config << std::endl;
	  //std::cout << "PrevStruct: " << prev_struct << std::endl;
	  conf_gen.set_configuration(prev_config, prev_struct);

	  // For each augmented structure...
	  for(unsigned k = 0; k < s_indices.size(); k++)
	    {
	      unsigned s_index = s_indices[k];

	      // Set clauses that encode the configuration being
	      // augmented and the selected structure
	      const structure & str = new_structs[s_index]._struct;

	      //std::cout << "Struct: " << str << std::endl;
	      conf_gen.set_structure(prev_config, str);	      

	      // If the innermost hull contains only the new
	      // point, then we should consider only the
	      // automorphisms of the prev_config. Otherwise, the
	      // new point is added to the innermost hull of the
	      // prev_config, so we should consider the previous
	      // automorphisms of the prev_config.
	      const std::vector<permutation_ptr> & pr_perms = str.back() == 1 ? prev_perms : prev_perms_p;

	      while(conf_gen.generate_next_configuration(new_config))
		{
		  new_perms.clear();
		  if(is_canonical(new_config, str.size(), pr_perms, size, new_perms))
		    {
		      //	      std::cout << "CANONICAL: " << new_config << std::endl;
		      count_configs++;
#ifndef PRINT
		      if(size != limit_size)
#endif
			{
			  // pr_perms are the previous automorphisms
			  // of new_config, and its own automorphisms
			  // are new_perms, return by is_canonical()
#ifdef PRINT
			  temp_configs[k].push_back(conf_data { new_config, s_index, pr_perms, new_perms });
#else
			  new_configs.push_back(conf_data { new_config, s_index, pr_perms, new_perms });
#endif
			}
		    }
		}	      
	    }

#ifdef PRINT
	  std::merge(temp_configs[0].begin(), temp_configs[0].end(),
		     temp_configs[1].begin(), temp_configs[1].end(),
		     back_inserter(new_configs),
		     [] (const auto & x, const auto & y) -> bool
		     {
		       return x._conf < y._conf;
		     });
	  
	  unsigned long limit = count_configs - c_conf;
	  unsigned long start = 0;
	  if(size != limit_size)
	    start = c_conf;
	  
	  for(unsigned long j = 0; j < limit; j++)
	    {
	      std::cout << 1 + c_conf + j << ": " << new_configs[start + j]._conf <<  std::endl;
	    }
	  if(size == limit_size)
	    new_configs.clear();
#else
	  if(i > 0 && i % 1000 == 0)
	    std::cout << "Processed " << i << " old configs" << std::endl;
#endif     
	}
#ifndef PRINT    
      std::cout << "Configs of size " << size << ": " << count_configs << " (num of structs: " << new_structs.size() << ")" << std::endl;
#endif
    }
}


int main(int argc, char ** argv)
{
  if(argc < 2)
    {
      std::cerr << "usage: " << argv[0] << " max_n" << std::endl;
      exit(1);
    }
  
  unsigned max_size = atoi(argv[1]);
  
  cyclic_store::init_instance(max_size);
  smallest_configurations::init_instance(max_size);
  
  enumerate_configurations(max_size);

  smallest_configurations::delete_instance();
  cyclic_store::delete_instance();
#ifdef _USE_SHARED_PTR
  permutation_memory::delete_instance();
#endif
  
  return 0;
}
