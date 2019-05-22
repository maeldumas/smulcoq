#ifndef ENIGME_H
#define ENIGME_H
#include <vector>
#include <string>

#define NB_PATTERN 6

class Enigme
{
 private :
  unsigned int nbcell;
  unsigned int nbp_min;
  unsigned int nbp_max;
  std::vector<std::string> affiches;
  std::string HN = "";
  std::string HY = "";
  std::string H = "";
  bool vide = false;

  std::vector<std::string> affichesT;
  std::string HYT = "";
  
  std::vector<std::vector<bool>> solution;

  // Génère l'hypothèse HN.
  void gen_HN();
  // Génère l'hypothèse du roi.
  void gen_HY1();
  //void gen_HY2();

  // C est conséquence des hypothèse ?
  bool consequenceH(std::string C);

  void unfoldH();
  std::string gen_terme();
  std::string contenu(std::string con, bool b, bool sp);
  std::string connecteur(std::string con);

  /* Génération des schéma pour les affiches.*/
  std::string pattern1(int i);
  std::string pattern2(int i);
  std::string pattern3(int i);
  std::string pattern4(int i);
  std::string pattern5(int i);
  std::string pattern6(int i);
  //std::string pattern7(int i);

  std::string patternT1(int i, int a1);
  std::string patternT2(int i, int a1, int a2);   


  
 public :
  Enigme(unsigned int n, bool vide = false);
  Enigme(unsigned int n, unsigned int min, unsigned int max, bool vide = false);
  Enigme(std::string filename);
    
  /* Il est nécessaire d'appeler "srand(time(NULL));" avant d'utiliser la méthode gen_affiches ou gen_affichesT. */
  // Génère des affiches indépendantes.
  void gen_affiches();
  // Génère des affiches dépendantes les unes des autres.
  void gen_affichesT();
  // Teste la validité de l'énigme et trouve la solution si elle existe.
  bool test_validite();

  
  // Affiche les diffèrents paramètres de l'énigme.
  void print(bool affichage = false);
  // Affiche la solution de l'énigme.
  void printSol();
  // Écrit le fichier Coq associé à l'énigme.
  void printV(std::string file_name = "enigme");
  // Écrit le fichier texte associé à l'énigme.
  void printT(std::string file_name = "enigme");
  // Écrit le fichier ppta associé à l'énigme.
  void printL(std::string file_name = "enigme");
};


#endif
  
