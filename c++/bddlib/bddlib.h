#ifndef _BDDLIB_H
#define _BDDLIB_H

struct solver_t;
typedef struct solver_t bddsolver;

struct obdd_st;
typedef struct obdd_st obdd_t;

extern bddsolver* solver_new(void);
extern void    solver_delete(bddsolver* s);
extern int    solver_addclause(bddsolver* s, int* begin, int* end);
extern int    solver_solve(bddsolver* s, int* begin, int* end);
extern int    solver_simplify(bddsolver* s);
extern void solver_reset(bddsolver * s);
extern obdd_t * get_root(bddsolver *s);
extern void solver_setpersistent(bddsolver * s);
extern int solver_npersistent(bddsolver * s);


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

extern void decompose_bdd(bdd_data * data);

extern void add_to_obdd_node_storage(obdd_t * freelist);

extern void release_obdd_storage(int final);


#endif // _BDDLIB_H
