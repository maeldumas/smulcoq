#include "enigme.h"
#include <iostream>
#include <regex>
#include <sstream>
#include <stdlib.h>
#include <fstream>

using namespace std;

void unfold(string& str, const string& from, const string& to) {
    if(from.empty())
        return;
    size_t start_pos = 0;
    while((start_pos = str.find(from, start_pos)) != std::string::npos) {
        str.replace(start_pos, from.length(), to);
        start_pos += to.length();
    }
}

string unfoldC(string str){
  unfold(str, "&", "&&");
  unfold(str, "|", "||");
  unfold(str, "->", "-->");
  unfold(str, "!", "negb ");
  return str;
}

string random_connecteur(){
  int n = rand()%4;
  string s;
  switch(n){
  case 0: {s = "&"; break;}
  case 1: {s = "|"; break;}
  case 2: {s = "->"; break;}
  case 3: {s = "<->"; break;}
  }
  return s;
}

Enigme::Enigme(unsigned int n, bool vide){
  this->nbcell = n;
  this->nbp_min = 0;
  this->nbp_max = nbcell;
  this->vide = vide;
  this->affiches = vector<string>(nbcell);
  this->affichesT = vector<string>(nbcell);
  this->gen_HN();
  this->gen_HY1();
  this->solution = vector<vector<bool>>(2);
  this->solution[0] = vector<bool>(nbcell);
  this->solution[1] = vector<bool>(nbcell);
}

Enigme::Enigme(unsigned int n, unsigned int min, unsigned int max, bool vide){
  this->nbcell = n;
  this->nbp_min = min;
  this->nbp_max = max;
  this->vide = vide;
  this->affiches = vector<string>(nbcell);
  this->affichesT = vector<string>(nbcell);
  this->gen_HN();
  this->gen_HY1();
  this->solution = vector<vector<bool>>(2);
  this->solution[0] = vector<bool>(nbcell);
  this->solution[1] = vector<bool>(nbcell);
}

Enigme::Enigme(string filename){
  //this->readfile(filename);
  ifstream in(filename, ios::in);
  if(!in.is_open()){
    cerr << "le fichier " << filename << "n'a pas pu être ouvert, arret du programme"<<endl;
    terminate();
  }
  string line;
  getline(in, line);
  this->vide = line=="V"?true:false;
  getline(in, line);
  this->nbcell = stoi(line);
  this->nbp_min = 0;
  this->nbp_max = nbcell;
  this->affiches = vector<string>(nbcell);
  this->affichesT = vector<string>(nbcell);
  this->gen_HN();
  this->solution = vector<vector<bool>>(2);
  this->solution[0] = vector<bool>(nbcell);
  this->solution[1] = vector<bool>(nbcell);
  for(int i = 0; i<nbcell; i++){
    getline(in, line);
    affiches[i] = line;
  }
  getline(in, line);
  this->HY = line;
  in.close();
}

void Enigme::printL(string file_name){
  ofstream out;
  file_name += ".ppta";
  out.open(file_name);
  
  out << (this->vide?"V":"NV") << endl;
  out << nbcell << endl;
  for(int i=0 ; i<nbcell; i++)
    out << affiches[i] << endl;
  out << HY << endl;

  out.close();
}


void Enigme::gen_HN(){
  stringstream ss;
  ss << "(";
  if(!vide)
  for(int i = 1; i <= nbcell; i++){
    ss << "((PC" << i << " & !TC" << i << ") | (!PC" << i << " & TC" << i << "))";
     if(i < nbcell)
      ss << " & ";
  }
  else
    for(int i = 1; i <= nbcell; i++){
      ss << "((PC" << i << " & !TC" << i << " & !VC" << i << ") | "
	 << "(!PC" << i << " & TC" << i << " & !VC" << i << ") | "
	 << "(!PC" << i << " & !TC" << i << " & VC" << i << "))";
      if(i < nbcell)
	ss << " & ";
    }
  ss << ")";
  this->HN = ss.str();
}

void Enigme::gen_HY1(){
  stringstream ss;
  ss << "(";
  for(int i = 1; i <= nbcell; i++){
    ss << "(PC" << i << " -> A" << i << ") & (TC" << i << " -> !A" << i << ")";
    if(vide)
      ss << " & (VC" << i << " -> (A" << i << " | !A" << i << "))";
    if(i < nbcell)
      ss << " & ";
  }
  ss << ")";

  if(nbp_min == 1 && nbp_max == 1){
    ss << " & (";
    for(int i = 1; i <= nbcell; i++) {
      ss << "(";
      for(int j = 1; j <= nbcell; j++){
	ss << (i==j?"":"!") << "PC" << j;
	if(j < nbcell)
	  ss << " & ";
      }
      ss << ")";
      if(i < nbcell)
	ss << " | ";
    }
    ss << ")";	  
  }

  HYT = "Si la cellule contient une princesse alors l'affiche dit la vérité, si la cellule contient un tigre alors l'affiche ment";
  HYT += (vide?" , si la cellule est vide alors l'affiche peut dire la vérité ou mentir.":".");
  
  HY = ss.str();
}

/*
void Enigme::gen_HY2(){
  stringstream ss;
  ss << "(";
  for(int i = 1; i <= nbcell; i++){
    if(i%2 == 1)
      ss << "(PC" << i << " -> A" << i << ") & (TC" << i << " -> !A" << i << ")";
    else
       ss << "(TC" << i << " -> A" << i << ") & (PC" << i << " -> !A" << i << ")";
    if(i < nbcell)
      ss << " & ";
  }
  ss << ")";
  HY = ss.str();
  }*/

//besoin de déclarer srand(time(NULL)) au préalable
void Enigme::gen_affiches(){
  int nb_pattern;
  for(int i = 1; i <= nbcell; i++){
    nb_pattern = rand()%NB_PATTERN + 1;
   switch(nb_pattern){
    case 1: {affiches[i-1] = pattern1(i); break;}
    case 2: {affiches[i-1] = pattern2(i); break;}
    case 3: {affiches[i-1] = pattern3(i); break;}
    case 4: {affiches[i-1] = pattern4(i); break;}
    case 5: {affiches[i-1] = pattern5(i); break;}
    case 6: {affiches[i-1] = pattern6(i); break;}
    }
  }
}

void Enigme::gen_affichesT(){
  int tp = nbcell, tf = nbcell-1;
  while(tf >= 1){
    int x = rand()%2 + 1;
    if(x == 1 || tf == 1){
      affiches[tp-1] = patternT1(tp, tf);
      tp--; tf--;
    }
    else{
      affiches[tp-1] = patternT2(tp, tf, tf-1);
      tp--; tf-=2;
    }
  }
  int nb_pattern;
  for(int i = tp; i >= 1; i--){
    nb_pattern = rand()%NB_PATTERN + 1;
    switch(nb_pattern){
    case 1: {affiches[i-1] = pattern1(i); break;}
    case 2: {affiches[i-1] = pattern2(i); break;}
    case 3: {affiches[i-1] = pattern3(i); break;}
    case 4: {affiches[i-1] = pattern4(i); break;}
    case 5: {affiches[i-1] = pattern5(i); break;}
    case 6: {affiches[i-1] = pattern6(i); break;}
    }
  }
}

void Enigme::unfoldH(){
  unfold(H, "HY", HY);
  unfold(H, "HN", HN);
  for(int i = nbcell; i >= 1; i--)
    unfold(H, "A" + to_string(i), affiches[i-1]);
}


bool Enigme::consequenceH(string C){
  ofstream file;
  string file_name = "sat.txt";
  file.open(file_name);
  file << (H + C);
  file.close();
  
  if(system("./limboole/limboole sat.txt -o ans.txt") == 32512){
    cerr << "Erreur : vérifiez que limboole soit bien dans votre dossier." << endl;
    exit (EXIT_FAILURE);
  }

  ifstream ansf;
  string answer;
  ansf.open("ans.txt");
  getline(ansf, answer);
  ansf.close();
   
  return answer == "% VALID formula";
} 

bool Enigme::test_validite(){
  H = "(" + HY + " & " + HN + ") -> ";
  unfoldH();
  string C;
  bool r=true, p, np;
  int i=1, nbp=0, nbt=0;
  while(i <= nbcell && r){
    C = "(PC" + to_string(i) + ")";
    p = consequenceH(C);
    C = "(!PC" + to_string(i) + ")";
    np = consequenceH(C);
    solution[0][i-1] = p;
    solution[1][i-1] = np;
    if(p == np)
      r = false;
    else
      if(p == true) nbp++;
    i++;
  }
  /*if(r)
    cout << "Enigme valide : " << r << endl
    << "Nombre de princesses :" << nbp << endl;*/
  return r && (nbp >= nbp_min) && (nbp <= nbp_max);
}

string Enigme::gen_terme(){
  if(vide){
    int n = rand()%3;
    if(n == 0) return "PC";
    if(n == 1) return "TC";
    else  return "VC";
  }
  else{
    int n = rand()%2;
    if(n == 0) return "PC";
    if(n == 1) return "TC";
  }
}

string Enigme::contenu(string con, bool b, bool sp){
  if(sp){
    if(con == "PC")
      if(b)
	return " contient une princesse";
      else
	return " ne contient pas de princesse";
    if(con == "TC")
      if(b)
	return " contient un tigre";
      else
	return " ne contient pas de tigre";
    if(con == "VC")
      if(b)
	return " est vide";
      else
	return " n'est pas vide";
  }
  else{
     if(con == "PC")
    if(b)
      return " contiennent une princesse";
    else
      return " ne contiennent pas de princesse";
  if(con == "TC")
    if(b)
      return " contiennent un tigre";
    else
      return " ne contiennent pas de tigre";
  if(con == "VC")
    if(b)
      return " sont vide";
    else
      return " ne sont pas vide";
  }
  
  return "";
}

string Enigme::pattern1(int i){
  stringstream ss;
  string c = this->gen_terme();
  int n = rand()%nbcell + 1;
  ss << "(" << c << n << ")";

  stringstream st;
  st << "La cellule " << n << contenu(c, true, true) << ".";
  affichesT[i-1] = st.str();
  
  return ss.str();
}

string Enigme::pattern2(int i){
  stringstream ss;
  string c = this->gen_terme();
  int n = rand()%nbcell + 1;
  ss << "(!" << c << n << ")";
  
  stringstream st;
  st << "La cellule " << n << contenu(c, false, true) << ".";
  affichesT[i-1] = st.str();
  
  return ss.str();
}

string Enigme::pattern3(int i){
  stringstream ss;
  string c1 = this->gen_terme(), c2 = this->gen_terme(); 
  int n = rand()%nbcell + 1;
  ss << "(!" << c1 << i << " & " << c2 << n << ") | ("<< c1 << n <<  " & !" << c2 << i << ")";

  stringstream st;
  st << "La cellule " << i << contenu(c1, true, true) << " et la cellule " << n << contenu(c2, false, true)
     << ", ou la cellule " << i << contenu(c1, false, true) << " et la cellule " << n << contenu(c2, true, true) << ".";
  affichesT[i-1] = st.str();
    
  return ss.str();
}

string Enigme::pattern4(int i){
  stringstream ss;
  string c1 = this->gen_terme(), c2 = this->gen_terme(); 
  int m = rand()%nbcell + 1;
  int n = rand()%nbcell + 1;
  ss << "(" << c1 << m << " & " << c2 << n <<")";

  stringstream st;
  st << "La cellule " << m << contenu(c1, true, true) << " et la cellule " << n << contenu(c2, true, true)<< ".";
  affichesT[i-1] = st.str();
    
  return ss.str();
}

string Enigme::pattern5(int i){
  int hz = rand()%(nbcell<=4?nbcell-1:4) + 2;
  int dec = rand()%hz;
 string c = this->gen_terme();
  stringstream ss;
  ss << "(";
  for(int j = (dec==0?hz:dec); j <= nbcell; j+=hz){
    ss << c << j;
    if(j+hz <= nbcell ) ss << " & ";
  }
  ss << ")";

  stringstream st;
  st << "Les cellules numérotées "<< hz << "k+"<< dec << contenu(c, true, false) << ".";
  affichesT[i-1] = st.str();

  return ss.str();
}

string Enigme::pattern6(int i){
  int hz = rand()%(nbcell<=4?nbcell-1:4) + 2;
  int dec = rand()%hz;
  string c = this->gen_terme();
  stringstream ss;
  ss << "(";
  for(int j = (dec==0?hz:dec); j <= nbcell; j+=hz){
    ss << c << j;
    if(j+hz <= nbcell ) ss << " | ";
  }
  ss << ")";

  stringstream st;
  st << "Au moins une des cellules numérotées "<< hz << "k+"<< dec << contenu(c, true, true) << ".";
  affichesT[i-1] = st.str();
  
  return ss.str();
}

/*string Enigme::pattern7(int i){
  stringstream ss;
  ss << "(PC" << (i==1?nbcell:i-1) << " & !PC" << i << " & !PC" << i%nbcell + 1 << ") | ";
  ss << "(!PC" << (i==1?nbcell:i-1) << " & PC" << i << " & !PC" << i%nbcell + 1 << ") | ";
  ss << "(!PC" << (i==1?nbcell:i-1) << " & !PC" << i << " & PC" << i%nbcell + 1 << ")";

  affichesT[i-1] = "toto";
  
  return ss.str();
  }*/

string Enigme::connecteur(string con){
  if(con == "&")
    return  " et ";
  if(con == "|")
    return " ou ";
  if(con == "->")
    return " implique que ";
  if(con == "<->")
    return " équivaut à ";
  return "";
}

string Enigme::patternT1(int i, int a1){
  stringstream ss;
  string c = this->gen_terme();
  string nega = (rand()%2==0?"!":""), negt = (rand()%2==0?"!":"");
  string con = "&";
  ss << "(" << nega << "A" << a1 << " " << con << " "
     << negt << c << i <<")";

  stringstream st;
  st << "L'affiche "<< a1 << (nega==""? " dit la vérité":" ment") << " et cette cellule" << contenu(c, (negt==""), true) << ".";
  affichesT[i-1] = st.str();
   
  return ss.str();
}

string Enigme::patternT2(int i, int a1, int a2){
  stringstream ss;
  string c = this->gen_terme();
  string negt = (rand()%2==0?"!":""), nega1 = (rand()%2==0?"!":""), nega2 = (rand()%2==0?"!":"");
  string con1 = random_connecteur(), con2 = "&";
  ss << "((" << nega1 << "A" << a1 << " " << con1
     << " " << nega2 << "A" << a2 << ") " << con2 << " "
     << negt << c << i <<")";

  stringstream st;
  st << "L'affiche "<< a1 << (nega1==""? " dit la vérité":" ment") << connecteur(con1) << "l'affiche "<< a2 << (nega2==""? " dit la vérité":" ment") <<", et cette cellule" << contenu(c, (negt==""), true) << ".";
  affichesT[i-1] = st.str();
  
  return ss.str();
}


void Enigme::print(bool affichage){
  if(affichage)cout << nbcell << endl;
  for(int i = 0; i < nbcell; i++)
    cout << affiches[i] << endl;
  if(affichage) cout << HN << endl << HY << endl;
  if(affichage) {
    for(int i = 0; i < nbcell; i++)
      cout << solution[0][i] << " ";
    cout << endl;
    for(int i = 0; i < nbcell; i++)
      cout << solution[1][i] << " ";
    cout << endl;
  }
}

void Enigme::printV(string file_name){
  ofstream out;
  file_name += ".v";
  out.open(file_name);
  out << "Require Import SMTCoq.SMTCoq." << endl
      << "Require Import Bool." << endl << endl;

  out << "Parameters";
  for(int i = 1; i <= nbcell; i++)
    out << " PC" << i;
  out << ": bool."<< endl;

  out << "Parameters";
  for(int i = 1; i <= nbcell; i++)
    out << " TC" << i;
  out << ": bool."<< endl;

  if(vide){
    out << "Parameters";
  for(int i = 1; i <= nbcell; i++)
    out << " VC" << i;
  out << ": bool."<< endl << endl;
  out << endl;
  }
  
  for(int i = 1; i <= nbcell; i++){
    out << "Definition A" << i << " : bool := " << unfoldC(affiches[i-1]) << "." << endl;
  }

  out << endl;
  out << "Definition HN : bool := " << unfoldC(HN) << "." << endl;
  out << "Definition HY : bool := " << unfoldC(HY) << "." << endl;
  out << endl;
  
  out << "Lemma solution : HY && HN -->";
  for(int i = 1; i < nbcell; i++)
    out << (solution[0][i-1]?" ":" negb ") << "PC" << i << " &&";
  out << (solution[0][nbcell-1]?" ":" negb ") << "PC" << nbcell << "." << endl;

  out << "Proof." << endl << "unfold HY, HN";
  for(int i = nbcell; i>= 1; i--)
    out << ", A" << i;
  out << "." << endl << "zchaff." << endl << "Qed." << endl;
      
  out.close();
}


void Enigme::printT(string file_name){
  ofstream out;
  file_name += ".txt";
  out.open(file_name);
  out << "Énigme de la princesse et du tigre" << endl << endl
      << "Il y a " << nbcell << " cellules." << endl
      << "Dans chaque cellule il y a soit une princesse, soit un tigre" << (vide?", soit elle est vide.":".") << endl
      << "Sur chaque cellule il y a une affiche avec une affirmation, une affiche peut mentir." << endl
      << "Le but est de trouver une cellule avec une princesse, ";
  if(nbp_max == nbp_min)
    out << "il y en a " << nbp_max << "." << endl;
  else
    out << "il y en a au moins " << nbp_min << " et au plus " << nbp_max << "." << endl;
  out << "On dispose aussi de la règle suivante : " << endl << HYT << endl << endl
      << "Les affiches sont les suivantes : " << endl;
  for(int i = 1; i <= nbcell; i++)
    out << "Affiche " << i << " : " << affichesT[i-1] << endl;
  out << endl << "Bon courage !" << endl;
}

void Enigme::printSol(){
  int cpt = 0;
  for(int i=0; i<nbcell; i++)
    if(solution[0][i])
      cpt++;
  if(cpt == 0)
    cout << "Il n'y a pas de princesse dans les cellules." << endl;
  else{
    if(cpt == 1)
      cout << "Il y a une princesse dans la cellule";
    else
      cout << "Il y a des princesses dans les cellules";

    bool s = false;
    for(int i=0; i<nbcell; i++)
      if(solution[0][i]){
	cout << (s?", ":" ") << i+1;
	s = true;
      }
    cout << "." << endl;
  }
}
