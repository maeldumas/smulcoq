# Smulcoq
Dépôt du projet Smullyan et le Coq réalisé dans le cadre d'un TER de Master 1 en informatique à l'Université de Montpellier.

### Modélisation des énigmes de la princesse et du tigre en Coq

Les modélisations en [Coq](https://coq.inria.fr/) de ces énigmes sont dans le dossier *model_enigme*.
Les modélisations avec `bool` utilise le plugin [SMTCoq](https://smtcoq.github.io/) qui doit être installé en plus de Coq.

### Installation du générateur d'énigme

Le code de `genigme` et `solvigme` est dans le dossier src. Pour compiler, utiliser la commande `make` dans le dossier *src*.
Le code utilise l'outil [Limboole](http://fmv.jku.at/limboole/), il est nécessaire de le télécharger et le compiler dans le dossier *src*. Le dossier contenant cet outil doit être nommé "limboole".

### Utilisation de genigme

Cet outil permet de générer des énigmes inspirées de celles de la princesse et du tigre. Si une énigme bien formée à été trouvée, alors trois fichiers sont produit :
- enigme.v : Fichier coq correspondant à l'énigme et dont la preuve est faites par SMTCoq.
- enigme.txt : Fichier texte correspondant à une interprétation en langage naturel de l'énigme.
- enigme.ppta : Fichier correspondant à l'énigme au format accepté par `solvigme`.
Notice de `genigme` :
```
usage: genigme <nbcell> [ <option> ... ]

  -h             Affiche cette aide et quitte.
  -vide          Permet d'avoir des cellules vide. 
  -af            Permet d'avoir un arbre d'affiches. 
                 (défaut : affiches indépendantes les unes des autres) 
  -o <file>      Les fichiers produit seront : file.v, file.txt, file.ppta. 
                 (défaut : file = enigme)  
  -t <time>      Timeout au bout de time secondes 
                 (défaut : time = 60)  

Attention : le nombre de cellules doit être plus grand que 2.
```

### Utilisation de solvigme

Cet outil permet tester si une énigme est bien formée, et si c'est le cas, affiche la liste des cellules qui contiennent une princesse.
Notice de `solvigme`
```
usage: solvigme <in-file> [ <option> ... ]

  -h                 Affiche cette aide et quitte.
  -coq <out-file>    Écrit le fichier coq associé à l'énigme dans un fichier out-file.v. 

Le format à respecter pour le fichier in-file est le suivant : 

V/NV       : V si l'énigme a des cellules vides, NV sinon. 
n          : nombre de cellules. 
(A1)       : La formule de l'affiche 1. 
(A2)       : La formule de l'affiche 2. 
... 
(An)       : La formule de l'affiche n. 
(H)        : L'hypothèse du roi et l'hypothèse de répartition si il y en a une. 

Attention à utiliser les bons connecteurs logiques (&,|,->,<->,!), 
à bien parenthéser les formules et à bien respecter l'ordre des affiches. 
```

Dans le dossier *exemples*, l'énigme 1 et 3 de la princesses et du tigre sont disponibles au format accepté par `solvigme`.
