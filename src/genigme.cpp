#include "enigme.h"
#include <iostream>
#include <fstream>
#include <chrono>

using namespace std;

#define USAGE \
"usage: genigme <nbcell> [ <option> ... ]\n" \
"\n" \
"  -h             Affiche cette aide et quitte.\n" \
"  -vide          Permet d'avoir des cellules vide. \n" \
"  -af            Permet d'avoir un arbre d'affiches. \n" \
"                 (défaut : affiches indépendantes les unes des autres) \n" \
"  -o <file>      Les fichiers produit seront : file.v, file.txt, file.ppta. \n" \
"                 (défaut : file = enigme)  \n" \
"  -t <time>      Timeout au bout de time secondes \n" \
"                 (défaut : time = 60)  \n" \
"\n" \
"Attention : le nombre de cellules doit être plus grand que 2. \n" \


int main(int argc, char *argv[]){
  chrono::time_point<chrono::system_clock> start, w;
  int es;
  start = chrono::system_clock::now();
  if(argc < 2)
    cout << USAGE;
  else{
    bool fin = false;
    srand (time(NULL));
    string arg = argv[1];
    if(arg == "-h" || stoi(arg) < 2){
	cout << USAGE;
	fin = true;
    }
    else {
    int nbcell = stoi(arg);
    bool t = false;
    bool v = false;
    string out_name = "enigme";
    int timeout = 60;
    
    for(int i=2; !fin && i<argc; i++){
      arg = argv[i];
      if(arg == "-h"){
	cout << USAGE;
	fin = true;
      }
      else if(arg == "-vide")
	v = true;
      else if(arg == "-af")
	t = true;
      else if(arg == "-o" && argc > i+1){
	out_name = argv[i+1];
	i++;
      }else if(arg == "-t" && argc > i+1){
	timeout = stoi(argv[i+1]);
	i++;
      }
      else{
	cout << USAGE;
	fin = true;
      }
    }
    
    if(!fin){
      cout << "Tentative de génération d'une énigme à " << nbcell << " cellules, une princesse, " << (v?"avec":"sans") << " cellules vides et " << (v?"avec":"sans") << " arbre d'affiches..." << endl;
      srand(time(NULL));
      bool trouve = false;
      Enigme e1(nbcell, 1, 1, v);
      int cpt = 0;
      w = chrono::system_clock::now();
      es = chrono::duration_cast<chrono::seconds>(w-start).count();
      while(!trouve && es < timeout){
	cpt++;
	t?e1.gen_affichesT():e1.gen_affiches();
	trouve = e1.test_validite();
	w = chrono::system_clock::now();
	es = chrono::duration_cast<chrono::seconds>(w-start).count();
      }

      w = chrono::system_clock::now();
      es = chrono::duration_cast<chrono::milliseconds>(w-start).count();
      if(trouve){
	e1.printV(out_name);
	e1.printT(out_name);
	e1.printL(out_name);

	cout << "Une énigme bien formée a été générée en " << cpt << " essai" << (cpt==1?"":"s") << " et " << es << "ms." << endl;
      }
      else
	cout << "Timeout : aucune énigme bien formée n'a été générée en " << cpt << " essai" << (cpt==1?"":"s") << " et " << es << "ms." << endl;
    }
  }
  }
  return 0;
}
