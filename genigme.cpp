#include "enigme.h"
#include <iostream>
#include <fstream>

using namespace std;

#define USAGE \
"usage: genigme <nbcell> [ <option> ... ]\n" \
"\n" \
"  -h             affiche cette aide et quitte\n" \
"  -vide          permet d'avoir des cellules vide \n" \
"  -t2            permet d'avoir des affiches de type 2 \n" \
"  -o <out-file>  fixe le nom du fichier (par défaut enigme, les fichiers produit par ce programme seront : enigme.v, enigme.txt, enigme.ppta) \n" \


int main(int argc, char *argv[]){
  if(argc < 2)
    cout << USAGE;
  else{
    bool fin = false;
    srand (time(NULL));
    int nbcell = atoi(argv[1]);
    bool t = false;
    bool v = false;
    string out_name = "enigme";

    for(int i=2; !fin && i<argc; i++){
      string arg = argv[i];
      if(arg == "-h"){
	cout << USAGE;
	fin = true;
      }
      else if(arg == "-vide")
	v = true;
      else if(arg == "-t2")
	t = true;
      else if(arg == "-o" && argc > i+1){
	out_name = argv[i+1];
	i++;
      }
      else{
	cout << USAGE;
	fin = true;
      }
    }
    
    if(!fin){
      srand (time(NULL));
      bool trouve = false;
      Enigme e1(nbcell, 1, 1, v);
      int cpt = 0;
      while(!trouve && cpt < 1000){
	cpt++;
	t?e1.gen_affichesT():e1.gen_affiches();
	trouve = e1.test_validite();
      }
      
      if(cpt < 1000){
	e1.printV(out_name);
	e1.printT(out_name);
	e1.printL(out_name);

	cout << "Une énigme bien formée a été générée en " << cpt << " essai" << (cpt==1?".":"s.") << endl;
      }
      else
	cout << "Aucune énigme bien formée à été générée en " << cpt << " essais." << endl;
	  }
  }
  return 0;
}
