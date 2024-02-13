# Categorical Logic! 

Based on [the lecture notes](https://awodey.github.io/catlog/notes/) from CMU 80514,
a course taught by [Professor Steve Awodey](https://awodey.github.io/).

## Done

* Define non-dependent products in a category (useful since having functions in the types sometimes gets in the way)
* Define signature
* Define term
* Define algebraic theory
* Define model of an algebraic theory in a category with finite products
* Prove that a model of the trivial algebraic theory in a category is equivalent to the category itself
* Prove that a model of the trivial 

## Todo

* Actually prove the equivalence to Exercise 1.1.9 in `CatLogic/AlgTheory/Constructions/MulAction.lean`
* Define model of a group
* Prove that groups in group are abelian groups (Exercise 1.1.14)
* Define the syntactic category of a theory
  * morphisms need some quotient type stuff, could be very annoying
  * models as functors
  * universal properties
* Clean things up if possible
  * proof of pointed types is nowhere close to clean
  * maybe there's a way to make all the HEq less of a mess
* All the actually important Lawvere stuff that I don't even touch yet
