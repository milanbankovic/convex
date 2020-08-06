#include "common.hpp"

struct conf_data_dfs {
  configuration _conf;
  structure _struct;
  std::vector<permutation_ptr> _eq_perms_p;
  std::vector<permutation_ptr> _eq_perms;
};


void print_progress(unsigned long new_count)
{
  static unsigned long last_printed_count = 0;
  static unsigned long count = 0;

  count += new_count;
  if(count - last_printed_count >= 1000)
    {
      std::cout << "Processed " << count << " old configs" << std::endl;
      last_printed_count = count;
    }
}

#if defined PRINT && !defined _PARALLEL
unsigned long dfs_enumerate(const conf_data_dfs & prev_cd, unsigned prev_size, unsigned limit_size, unsigned long counter)
#else
  unsigned long dfs_enumerate(const conf_data_dfs & prev_cd, unsigned prev_size, unsigned limit_size)
#endif
{
  auto lambda = [] ()
		{
		  std::vector<std::shared_ptr<configuration_generator>> conf_gens;
		  for(unsigned k = 0; k <= 12; k++)
		    conf_gens.push_back(std::make_shared<configuration_generator>(k));
		  return conf_gens;
		};

#ifndef _PARALLEL
  static std::vector<std::shared_ptr<configuration_generator>> conf_gens = lambda();
#else
  static tbb::combinable<std::vector<std::shared_ptr<configuration_generator>>> conf_gens_comb(lambda);
  std::vector<std::shared_ptr<configuration_generator>> & conf_gens = conf_gens_comb.local();
#endif
  
  const configuration & prev_config = prev_cd._conf;
  const std::vector<permutation_ptr> & prev_perms  = prev_cd._eq_perms;
  const std::vector<permutation_ptr> & prev_perms_p = prev_cd._eq_perms_p;
  const structure & prev_struct = prev_cd._struct;
  unsigned size = prev_size + 1;
  unsigned long count_configs = 0;
  
  configuration_generator & conf_gen = *conf_gens[size];
  
  conf_gen.set_configuration(prev_config, prev_struct);
  
  // Calculation of augmented structures
  std::vector<structure> augmented_structs;
  augmented_structs.push_back(prev_struct);
  augmented_structs.back().back()++;
  if(prev_struct.back() >= 3)
    {
      augmented_structs.push_back(augmented_structs.back());
      augmented_structs.back().back()--;
      augmented_structs.back().push_back(1);
    }	  	      

#if defined PRINT && !defined _PARALLEL
  std::vector<conf_data_dfs> temp_configs[2];
#endif

  std::vector<permutation_ptr> new_perms;
  std::vector<conf_data_dfs> new_configs;
  
  // For each augmented structure...
  for(unsigned k = 0; k < augmented_structs.size(); k++)
    {

      // Set clauses that encode the configuration being
      // augmented and the selected structure
      const structure & str = augmented_structs[k];
      
      conf_gen.set_structure(prev_config, str);	      
      
      // If the innermost hull contains only the new
      // point, then we should consider only the
      // automorphisms of the prev_config. Otherwise, the
      // new point is added to the innermost hull of the
      // prev_config, so we should consider the previous
      // automorphisms of the prev_config.
      const std::vector<permutation_ptr> & pr_perms = str.back() == 1 ? prev_perms : prev_perms_p;
      configuration new_config = smallest_configuration(size);
      
      while(conf_gen.generate_next_configuration(new_config))
	{
	  new_perms.clear();
	  if(is_canonical(new_config, str.size(), pr_perms, size, new_perms))
	    {
	      count_configs++;
#if !defined PRINT || defined _PARALLEL
	      if(size != limit_size)
#endif
		{
		  // pr_perms are the previous automorphisms
		  // of new_config, and its own automorphisms
		  // are new_perms, return by is_canonical()
#if defined PRINT && !defined _PARALLEL
		  temp_configs[k].push_back(conf_data_dfs { new_config, str, pr_perms, new_perms });
#else
		  new_configs.push_back(conf_data_dfs { new_config, str, pr_perms, new_perms });
#endif
		}
	    }
	}	      
    }
  
#if defined PRINT && !defined _PARALLEL
  std::merge(temp_configs[0].begin(), temp_configs[0].end(),
	     temp_configs[1].begin(), temp_configs[1].end(),
	     back_inserter(new_configs),
	     [] (const auto & x, const auto & y) -> bool
	     {
	       return x._conf < y._conf;
	     });
#endif

    
  if(size != limit_size)
    {
#if !defined PRINT || defined _PARALLEL
      if(size == limit_size - 1)
	print_progress(new_configs.size());
#endif
      
#ifndef _PARALLEL
      count_configs = 0;
      for(const conf_data_dfs & cd : new_configs)
	{
#ifdef PRINT
	  count_configs += dfs_enumerate(cd, size, limit_size, counter + count_configs);
#else
	  count_configs += dfs_enumerate(cd, size, limit_size);
#endif
	}
#else
      count_configs = tbb::parallel_reduce(tbb::blocked_range<unsigned long>(0, new_configs.size()), 0UL,
					   [&new_configs, size, limit_size](const tbb::blocked_range<unsigned long> & r, unsigned long x) -> unsigned long
					   {
					     for(unsigned long i = r.begin(), end = r.end(); i != end; ++i)
					       {
						 x += dfs_enumerate(new_configs[i], size, limit_size);
					       }
					     return x;
					   },
					   [](unsigned long x, unsigned long y) -> unsigned long
					   {
					     return x + y;
					   });      
#endif      
    }
#if defined PRINT && !defined _PARALLEL
  else
    {
      for(unsigned long j = 0; j < new_configs.size(); j++)
	{
	  std::cout << counter + j + 1 << ": " << new_configs[j]._conf <<  std::endl;
	}
    }
#endif
  return count_configs;
}

void enumerate_configurations_dfs(unsigned limit_size)
{
  if(limit_size == 3)
    {
#if !defined PRINT || defined _PARALLEL
      std::cout << "Configs of size 3: 1" << std::endl;
#else
      std::cout << "1: -" << std::endl;
#endif
      return;
    }

#if defined PRINT && !defined _PARALLEL
  unsigned long count = dfs_enumerate(conf_data_dfs { { false }, structure { 3 }, {}, cyclic_permutations(3) },  3, limit_size, 0);
#else
  unsigned long count = dfs_enumerate(conf_data_dfs { { false }, structure { 3 }, {}, cyclic_permutations(3) },  3, limit_size);
  std::cout << "Configs of size " << limit_size << ": " << count << std::endl;
#endif
}

int main(int argc, char ** argv)
{
  if(argc < 2)
    {
#ifndef _PARALLEL
      std::cerr << "usage: " << argv[0] << " max_n" << std::endl;
#else
      std::cerr << "usage: " << argv[0] << " max_n [num_of_threads]" << std::endl;
#endif
      exit(1);
    }

  
  unsigned max_size = atoi(argv[1]);

#ifdef _PARALLEL
  unsigned num_of_threads = 0;
  if(argc >= 3)
    {
      num_of_threads = atoi(argv[2]);
    }
  tbb::task_scheduler_init ts(num_of_threads != 0 ? num_of_threads : tbb::task_scheduler_init::default_num_threads());
#endif
      
  cyclic_store::init_instance(max_size);
  smallest_configurations::init_instance(max_size);
  
  enumerate_configurations_dfs(max_size);

  smallest_configurations::delete_instance();
  cyclic_store::delete_instance();
#if defined _USE_SHARED_PTR && !defined _PARALLEL
  permutation_memory::delete_instance();
#endif

  
  return 0;
}
