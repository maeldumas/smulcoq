#include "enigme.h"
#include <iostream>
#include <fstream>

using namespace std;

#define USAGE \
"usage: genigme <in-file> [ <option> ... ]\n" \
"\n" \
"  -h                 affiche cette aide et quitte\n" \
"  -coq <out-file>    écrit le fichier coq associé à l'énigme dans un fichier out-file.v \n" \
"\n" \
"Le format à respecter pour le fichier in-file est le suivant : \n" \
"V ou NV selon si l'énigme possède des cellules vide(V) ou non (NV). \n" \
"n          : nombre de cellules. \n" \
"(A1)       : La formule de l'affiche 1. \n" \
"(A2)       : La formule de l'affiche 2. \n" \
"... \n" \
"(An)       : La formule de l'affiche n. \n" \
"(H)         : L'hypothèse du roi et l'hypothèse de répartition si il y en a une. \n" \
"\n" \
"Attention à utiliser les bons connecteurs logiques (&,|,->,<->,!), à bien paranthéser les formules et à bien respecter l'ordre des affiches. \n" \

int main(int argc, char *argv[]){
  if(argc < 2)
    cout << USAGE;
  else{
    string input_file = argv[1];
    string out_name;      
    bool coq = false;
    bool fin = false;
    if(input_file == "-h"){
	cout << USAGE;
	fin = true;
    }
    for(int i=2; !fin && i<argc; i++){
      string arg = argv[i];
      if(arg == "-h"){
	cout << USAGE;
	fin = true;
      }
      else if(arg == "-coq" && argc > i+1){
	coq = true;
	out_name = argv[i+1];
	i++;
      }
      else{
	cout << USAGE;
	fin = true;
      }
    }

    if(!fin){
      Enigme e1(input_file);
      if(e1.test_validite()){
	e1.printSol();
	if(coq)
	  e1.printV(out_name);
      }
      else
	cout << "L'énigme "<< input_file << " n'a pas de solution ou le fichier n'est pas bien formé" << endl;
    }
  }

  return 0;
}
