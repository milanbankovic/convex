#include <iostream>
#include <fstream>
#include <cstring>
#include "dpll.hpp"

using namespace std;

/* Funkcije za citanje ulaznog fajla u DIMACS formatu */

/* Funkcija preskace beline i vraca ASCII kod prvog 
   karaktera koji nije belina */
int skipSpaces(istream & istr)
{
  int c;
  while((c = istr.get()) == ' ' || c == '\t' || c == '\n');
  return c;
}

/* Funkcija preskace ostatak linije (zgodno za preskakanje komentara) */
void skipRestOfLine(istream & istr)
{
  while(istr.get() != '\n');
}

/* Funkcija cita DIMACS format iz fajla datog ulaznim tokom istr. Ucitanu 
   formulu smesta u f, a broj varijabli u num_of_vars. */
bool readDIMACS(std::vector<clause> & f, unsigned & num_of_vars, istream & istr)
{
  unsigned num_of_clauses;
  int c;

  // Preskace komentare
  while((c = skipSpaces(istr)) == 'c')
    skipRestOfLine(istr);

  // Cita liniju p cnf nvars nclauses
  if(c != 'p')
    return false;
  else
    {
      string s;
      istr >> s;
      if(s != "cnf")
	return false;
      
      istr >> num_of_vars;
      istr >> num_of_clauses;
    }

  // Citamo klauze
  for(unsigned i = 0; i < num_of_clauses; i++)
    {
      clause c;
      int n;
      istr >> n; 
      while(!istr.eof() && !istr.fail() && n != 0)
	{
	  c.push_back(lit_from_int(n));
	  istr >> n;
	}
      
      if(istr.eof() || istr.fail())
	return false;

      f.push_back(c);
    }
  return true;
}


int main(int argc, char ** argv)
{
  unsigned num_of_vars;
  std::vector<clause> f;

  std::istream * istr = nullptr;
  std::ifstream file;
  bool print_solutions = true;
  bool all_sat = false;
  
  for(unsigned i = 1; i < argc; i++)
    {
      if(strcmp(argv[i], "-h") == 0)
	{
	  std::cout << "usage: " << argv[0] << " [-h] [-n] [--all] [input_file]" << std::endl;
	  exit(0);
	}
      else if(strcmp(argv[i], "-n") == 0)
	{
	  print_solutions = false;
	}
      else if(strcmp(argv[i], "--all") == 0)
	{
	  all_sat = true;
	}
      else if(argv[1][0] == '-')
	{
	  std::cout << "unrecognized option: " << argv[i] << std::endl;
	  exit(1);
	}
      else if(istr == nullptr)
	{
	  file.open(argv[i]);
	  istr = &file;
	}
    }      
  
  if(istr == nullptr)
    istr = &cin;
  
  if(!readDIMACS(f, num_of_vars, *istr))
    {
      cerr << "Error reading input file" << endl;
      exit(1);
    }

  solver sl(num_of_vars);
  sl.add_clauses(f);
  sl.set_units();
  sl.set_watch_lists();
  sl.simplify_clauses();

  if(!all_sat)
    {  
      if(!sl.solve())
	{
	  cout << "UNSAT" << endl;
	}
      else
	{
	  cout << "SAT" << endl;
	  if(print_solutions)
	    sl.val().print_stack(cout);
	}
    }
  else
    {
      unsigned long count_sols = 0;
      while(sl.solve())
	{
	  count_sols++;
	  if(print_solutions)
	    {
	      sl.val().print_stack(cout);
	      cout << endl;
	    }
	}
      cout << "SOLUTIONS: " << count_sols << endl;
    }

  return 0;
}
