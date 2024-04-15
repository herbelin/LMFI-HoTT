# Introduction to Homotopy Type Theory (LMFI 2023-2024)

<h2>Schedule</h2>

- Tuesday April 16, 14h00-17h00, room 1020 Sophie Germain
- Thursday April 18, 9h00-12h00, room 1020 Sophie Germain
- Tuesday April 23, 9h00-12h00, room 266 Olympe de Gouges
- Thursday April 25, 9h00-12h00, salle 2012 Sophie Germain

<h2>Plan prospectif</h2>

<h4>Cours 1 : Généralités sur la théorie des types</h4>

- La correspondance de Curry-Howard
  - une correspondance entre syntaxe intrinsèque et extrinsèque
  - propositions vues comme types « proof-irrelevant »
- Comparaison entre types simples et types dépendants
  - la correspondance fibrée/indexée
- Comparaison avec la théorie des ensembles
  - intrication calcul/logique (à la Church, à la ML, à la théorie des types) vs
    séparation totale calcul/logique (à la Curry, à la Lisp, à la ZF)
  - les ensembles vus comme arbres inductifs ou coinductifs (les ensemble de Aczel)
- La théorie des types comme jeu de légo
  - les différents types : ∑, Π, =, inductifs, coinductifs, troncation, univers
  - les règles de construction : formation, introduction, élimination, β-réduction, η-conversion
- Les différentes formes d'égalité
  - intensionnelle/extensionnelle
  - définitionnelle/propositionnelle
- Implémentations de la théorie des types
  - comparaison entre les logiques d'Agda, Coq, Isabelle, Lean, Mizar, ...
  - décidabilité de l'égalité définitionnelle
- Exercices

<h4>Cours 2 : Généralités sur la théorie des types homotopiques</h4>

- Type = espace à homotopie près, égalité = chemin
- h-niveaux de Voevodsky
  - une reconstruction des propositions, ensembles, groupoïdes comme types
- Les types inductifs supérieurs
  - exemples du cercle et de la sphère (homotopie synthétique)
  - exemple des types quotients
- Le principe d'univalence
  - les différentes définitions d'équivalence
  - l'univalence comme principe d'extensionnalité généralisation l'extensionnalité des propositions
- Axiome du choix
  - l'axiome du choix de Martin-Löf
  - prouvabilité du choix unique
  - l'axiome du choix général comme distribution du produit dépendant sur la troncation
  - l'axiome du choix implique la logique classique (théorème de Diaconescu)
- Exercices

<h4>Cours 3 : Modèles géométriques et catégoriques de la théorie des types</h4>

- La correspondance Curry-Howard-Lambek et son extension à la géométrie
- Un modèle « syntaxique » : les catégories avec familles
- L'interprétation des types dépendants comme « fibrations »
- Catégories cartésiennes localement fermées
- Les correspondances intrinsèque/extrinsèque et fibrée/indexée en action
- Univers vus comme classificateur d'objets
- ∞-catégories et ∞-groupoïdes
- Les différentes formes géométriques
  - globes (= itération de l'égalité homogène)
  - triangles/simplexes
  - cubes (= itération de l'égalité hétérogène)
  - opétopes
- Les différents équipements de structures
  - l'infrastructure pure de dépendances (structure « semi- »)
  - dégénérescences = réfléxivités = identités
  - complétion des cornets internes = transitivité = composition (structure de Kan faible)
  - complétion de tous les cornets = ajout de symétries = ajout d'inverses (structure de Kan forte)
- Exercices

<h4>Cours 4 : Théorie des types cubiques</h4>

- La théorie des types cubiques ou comment calculer avec la théorie des types homotopiques
  - l'univalence comme algorithme de réécriture de preuves sur une structure en preuves sur structures équivalentes
  - fonctions sur types inductifs supérieurs comme fonctions réécrivant des preuves d'égalités
- Paramétricité et réalisabilité au cœur de la correspondance intrinsèque/extrinsèque
- La paramétricité itérée comme génératrice des ensembles simpliciaux et cubiques
- Exemples de raisonnement égalitaire en théorie des types cubiques
- Comparaison avec la théorie des types observationnelle supérieure
- Exercices

Le cours, fait au tableau, laissera cependant la place à
l'improvisation en fonction des demandes de l'auditoire.

<h2>Lecture notes</h2>

<ul>                                                                                                                                                                 <li> <a charset="UTF-8" href="https://github.com/herbelin/LMFI-HoTT/blob/master/Lecture_notes/ITT.pdf">
Notes on Type Theory
</a></li>

<li> <a charset="UTF-8" href="https://github.com/herbelin/LMFI-HoTT/blob/master/Synthetic_Homotopy_Theory/Lecture_notes/Lecture_notes.pdf">
Lecture Notes on Synthetic Homotopy Theory
</a></li>
</ul>

<h2>Bibliography</h2>
<ul>

<li><a href="https://homotopytypetheory.org/book/">HoTT Book</a>, 2013</li>

<li><a href="https://arxiv.org/pdf/1703.03007.pdf">Homotopy type theory: the logic of space</a>, Michael Shulman, 2017</li>

<li><a href="https://www.andrew.cmu.edu/user/erijke/hott/hott_intro.pdf">Introduction to homotopy type theory</a>, Egbert Rijke, 2018</li>

<li>Pierre-Louis Curien's LMFI lectures on the <a href="https://curien.galene.org/notes/CoursA.pdf">syntax of Martin-Löf's type theory</a>, the <a href="https://curien.galene.org/notes/CoursB.pdf">categorical interpretation of extensional type theory</a> and <a href="https://curien.galene.org/notes/CoursC.pdf">homotopy type theory</a></li>
<li><a href="https://github.com/HoTT/HoTT">A HoTT library in Coq</a></li>

<li><a href="https://github.com/HoTT/HoTT-Agda">A HoTT library in Agda</a></li>

<li><a href="https://github.com/UniMath/UniMath">The UniMath library for "Univalent Foundations" in Coq</a></li>

<li><a href="https://github.com/barras/cic-model">Set theory in type theory</a></li>

<li><a href="http://www.cse.chalmers.se/~bengt/papers/hlcs.pdf">Martin-Löf’s Type Theory</a>,
B. Nordström, K. Petersson and J. M. Smith, 2000</li>

<li><a href="https://akaposi.github.io/finitaryqiit.pdf">Constructing Quotient Inductive-Inductive Types</a>,
Ambrus Kaposi, András Kovács, Thorsten Altenkirch</li>

</ul>
