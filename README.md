# Projet Evaluateur-Typeur de Lambda-Calcul

## Auteurs
* DIALLO Elhadj Alseiny
* N° : 21314810

### MU5IN555 TAS - Session 2024


## Structure du Projet

```bash
.
├── ast.ml               # Fonctions de base des termes
├── structure.ml    
├── type.ml              # Gestion des types et système d'unification
├── makefile   
├── README
└── tests                 # Dossier contenant les tests
│   ├── astTests.ml       # Tests liés à l'AST
│   ├── typeTests.ml      # Tests pour le typage
```

## Fonctionnalités Effectuées

### 1. Évaluateur pour un λ-calcul pur
#### λ-termes  aborder :

•	Les concepts fondamentaux : variables (Var), applications (App) et abstractions (Abs).
•	Les extensions numériques : manipulation des entiers (Int), addition (Add), soustraction (Sub).
•	La gestion des listes : construction (Cons), liste vide (Nil), accès à la tête (Head) et à la queue (Tail).
•	Les constructions conditionnelles : IfZero (condition sur zéro) et IfEmpty (condition sur liste vide).
•	Des fonctionnalités avancées : point fixe (Fix) pour la récursivité et le Let pour définir des variables locales.
•	Les traits impératifs : références mutables (Ref), déréférencement (Deref), et affectation (Assign).

#### Fonctionnalités implémentées :
•	Représentation des λ-termes 
•	Pretty Printer
•	Renommage des variables liées.
•	Substitution 
•	Réduction Call-by-Value (LtR-CbV) 
•	Normalisation 
•	Tests 

---

### 2. Types simples pour le λ-calcul

•	Génération d’équations de typage à partir des termes du λ-calcul.
•	Vérification Occur Check pour éviter les boucles infinies dans l’unification.
•	Substitution dans les types pour remplacer une variable de type par un autre type.
•	Étape d’unification pour traiter une contrainte dans un système d’équations.
•	Résolution complète d’un système d’équations avec gestion des timeouts.
•	Tests exhaustifs pour valider les processus de typage.

---

### 5. Extensions (Facultatives)

- [x] **5.5.** Implémenter la gestion des exceptions.

### Difficultés rencontrées
• Gestion de mémoire (évaluation, section 5.1) : Je n’ai pas réussi à concrétiser l’évaluation des références et des régions mémoire. Bien que les concepts soient expliqués dans la documentation, la mise en œuvre s’est avérée complexe.

•	Types polymorphes : La gestion des types polymorphes a entraîné des problèmes dans les versions précédentes, notamment en raison de la complexité des éditions nécessaires pour intégrer ce concept tout en maintenant la cohérence avec les autres parties du projet.

•	Tests insuffisants : Je n’ai pas pu poursuivre les tests de manière satisfaisante, car trouver et réduire des exemples à la main s’est révélé très pénible. Je me suis retrouvé à solliciter fréquemment ChatGPT pour générer des termes et les résultats attendus, sans avoir de moyen fiable de vérifier leur validité. Cela a souvent mené à chercher des bogues inexistants lorsque les réponses générées étaient incorrectes, ce qui m’a conduit à arrêter les tests. De plus, la librairie oUnit n’a pas pu être utilisée sur mon environnement macOS. Bien qu’elle ait été installée correctement, elle semble incompatible avec la version d’OCaml que j’utilise ou s’est installée sur une autre version d’OCaml présente sur mon ordinateur.
### Aide a assistant
    
• ChatGPT a été utilisé pour générer des exemples de code dans les parties les plus complexes du projet, notamment pour les tests. J’ai sollicité l’IA pour produire des termes et leurs résultats attendus, ce qui m’a permis de tester certaines fonctionnalités. J’ai également fourni à Rachid une fonction (* qui traduit un entier Church en entier normal *), qu’il a mentionnée dans son rapport. En complément, j’ai utilisé l’IA pour corriger des fautes, affiner mes commentaires, mieux comprendre les messages d’erreur dans les piles d’appels, ainsi que pour bénéficier d’une assistance d’auto-complétion installée sur mon IDE.

## commandes de compilation

### Pour lancer l'évaluateur
```bash
make run_ast 
```

### Pour lancer les tests de l'évaluateur
```bash
make run_tests_ast
```

### Pour lancer le typeur
```bash
make run_type
```

### Pour lancer les tests du typeur
```bash
make run_tests_type
```

### Pour nettoyer les fichiers de compilation
```bash
make clean
```



