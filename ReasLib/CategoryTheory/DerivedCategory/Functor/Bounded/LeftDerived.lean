module

public import ReasLib.CategoryTheory.DerivedCategory.Functor.Bounded.LeftDerived.Comparison
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Bounded.LeftDerived.Comparison.Naturality
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Bounded.LeftDerived.Canonical
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Bounded.LeftDerived.Value
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Bounded.LeftDerived.Naturality
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Bounded.LeftDerived.Naturality.Iso
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Bounded.LeftDerived.Degree.Naturality
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Bounded.LeftDerived.HomologicalDegree.Naturality
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Bounded.LeftDerived.HomologicalDegree.Comparison
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Bounded.LeftDerived.Naturality.Degree
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Bounded.LeftDerived.Naturality.HomologicalDegree
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Bounded.LeftDerived.Cochain
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Bounded.LeftDerived.Cochain.Naturality
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Bounded.LeftDerived.Properties

@[expose] public section

/-!
# Bounded-Above Left Derived Functors

Convenience import for the reusable bounded-above left-derived API.  Import a
narrower leaf when only one layer is needed:

* `LeftDerived.Comparison` for arbitrary models and their degree-zero
  comparison, and `LeftDerived.Comparison.Naturality` for the natural
  comparison between localization and canonical-single presentations;
* `LeftDerived.Canonical` for the standard total-derived functor and counit;
* `LeftDerived.Naturality` and `LeftDerived.Naturality.Iso` for
  transformations and isomorphisms of canonical models;
* `LeftDerived.{Degree,HomologicalDegree}.Naturality` for arbitrary-model
  degreewise functoriality, and `LeftDerived.Naturality.{Degree,HomologicalDegree}`
  for the canonical integer- and natural-number-indexed interfaces;
* `LeftDerived.HomologicalDegree.Comparison` for a direct `Lₙ` model
  comparison without repeated integer coercions or negation;
* `LeftDerived.Cochain` and `LeftDerived.Cochain.Naturality` for canonical
  maps out of derived values and their compatibility with functoriality;
* `LeftDerived.Value` for the value functor, its object and morphism
  projections, and their identity/composition computation laws, parameterized
  by a chosen localization model;
* `LeftDerived.Properties` for vanishing and right-exactness criteria.
-/
