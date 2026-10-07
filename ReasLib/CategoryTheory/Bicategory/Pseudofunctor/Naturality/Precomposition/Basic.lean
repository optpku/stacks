module

public import ReasLib.CategoryTheory.Bicategory.Pseudofunctor.Naturality.Precomposition.StrongTrans
public import ReasLib.CategoryTheory.Bicategory.Pseudofunctor.Naturality.Precomposition.Modification
public import ReasLib.CategoryTheory.Bicategory.Pseudofunctor.Naturality.Precomposition.Hom
public import ReasLib.CategoryTheory.Bicategory.Pseudofunctor.Naturality.Precomposition.Pseudofunctor

/-!
# Precomposition in pseudofunctor bicategories

Compatibility aggregate for precomposition of strong transformations,
modifications, functor-bicategory homs, and the induced strict
pseudofunctor. New developments should import the smallest leaf appropriate to
their use:

* `Precomposition.StrongTrans` for strong transformations;
* `Precomposition.Modification` for modifications;
* `Precomposition.Hom` for hom-category functors; or
* `Precomposition.Pseudofunctor.Basic` or `.Computations` for the global
  pseudofunctor and its projection formulas.
-/
