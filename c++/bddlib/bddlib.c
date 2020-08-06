#include "solver.h"

volatile sig_atomic_t eflag = 0;
static void SIGINT_handler(int signum)
{
	eflag = 1;
}


struct bdd_data {
  int n;
  int * a;
  obdd_t ** b;
  obdd_t * p;
  int s;
  int t;
  int done;
  int sol_found;
  int first_time;
};

obdd_t * get_root(solver * s)
{
  return s->root;
}

void decompose_bdd(struct bdd_data * data)
{
  data->sol_found = 0;

  do {

    if(data->first_time == 0)
      {
	if(data->t <= 0) { // b is empty
	  data->done = 1;
	  return;
	}
	
	data->p = data->b[--data->t]; 
	while(data->a[--data->s] > 0) ;
	data->a[data->s] = abs(data->a[data->s]); data->s++;
	data->p = data->p->hi;
      }
    else
      data->first_time = 0;	
    
    while(!(data->p == obdd_bot() || data->p == obdd_top())) {
      data->b[data->t++]  = data->p;
      data->a[data->s++]  = -(data->p->v);
      data->p       = data->p->lo;
    }
    if(data->p == obdd_top())
      {
	data->sol_found = 1;
      }
    
  } while(data->sol_found == 0);
}
