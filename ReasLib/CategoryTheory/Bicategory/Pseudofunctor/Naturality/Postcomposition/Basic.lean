module

public import ReasLib.CategoryTheory.Bicategory.Pseudofunctor.Naturality.Postcomposition.StrongTrans
public import ReasLib.CategoryTheory.Bicategory.Pseudofunctor.Naturality.Postcomposition.Modification
public import ReasLib.CategoryTheory.Bicategory.Pseudofunctor.Naturality.Postcomposition.Hom
public import ReasLib.CategoryTheory.Bicategory.Pseudofunctor.Naturality.Postcomposition.Pseudofunctor

/-!
# Postcomposition in pseudofunctor bicategories

Compatibility aggregate for postcomposition of strong transformations,
modifications, functor-bicategory homs, and the induced pseudofunctor. New
developments should import the smallest leaf appropriate to their use:

* `Postcomposition.StrongTrans` for strong transformations;
* `Postcomposition.Modification` for modifications;
* `Postcomposition.Hom` for hom-category functors; or
* `Postcomposition.Pseudofunctor.Basic` or `.Computations` for the global
  pseudofunctor and its projection formulas.
-/
