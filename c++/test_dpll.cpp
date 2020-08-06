#include <iostream>
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


int main()
{
  unsigned num_of_vars;
  std::vector<clause> f;
  
  if(!readDIMACS(f, num_of_vars, cin))
    {
      cerr << "Error reading input file" << endl;
      exit(1);
    }

  solver sl(num_of_vars);
  sl.initialize_solver(f);
  
  if(!sl.solve())
    {
      cout << "UNSAT" << endl;
    }
  else
    {
      cout << "SAT" << endl;
      sl.val().print_stack(cout);
      cout << sl.val().current_level() << endl;
    }

  return 0;
}
