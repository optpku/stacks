/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.DerivedCategory.Functor.Bounded.RightDerived.Comparison
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Bounded.RightDerived.Comparison.Naturality
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Bounded.RightDerived.Canonical
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Bounded.RightDerived.Value
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Bounded.RightDerived.Value.Naturality
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Bounded.RightDerived.Value.Naturality.Iso
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Bounded.RightDerived.PointwiseValue
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Bounded.RightDerived.PointwiseValueNaturality
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Bounded.RightDerived.PointwiseValueNaturalityIso
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Bounded.RightDerived.Naturality
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Bounded.RightDerived.Naturality.Iso
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Bounded.RightDerived.Degree.Naturality
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Bounded.RightDerived.Degree.InjectiveResolution
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Bounded.RightDerived.Naturality.Degree
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Bounded.RightDerived.Cochain
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Bounded.RightDerived.Cochain.Naturality
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Bounded.RightDerived.DeltaFunctor
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Bounded.RightDerived.DeltaFunctor.Naturality
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Bounded.RightDerived.DeltaFunctor.Naturality.Iso
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Bounded.RightDerived.DeltaFunctor.Connecting
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Bounded.RightDerived.DeltaFunctor.Sequence
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Bounded.RightDerived.DeltaFunctor.Sequence.Augmented
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Bounded.RightDerived.DeltaFunctor.Sequence.Augmented.Naturality
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Bounded.RightDerived.DeltaFunctor.Sequence.Augmented.Functoriality
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Bounded.RightDerived.DeltaFunctor.Sequence.Naturality
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Bounded.RightDerived.DeltaFunctor.Sequence.Functoriality
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Bounded.RightDerived.Properties
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Bounded.RightDerived.Universality
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Bounded.RightDerived.Cohomology
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Bounded.RightDerived.Cohomology.Naturality
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Bounded.RightDerived.Cohomology.Naturality.Iso

@[expose] public section

/-!
# Bounded-Below Right Derived Functors

This aggregate import provides the reusable bounded-below right-derived
functor API.  Import a narrower leaf when only one layer is needed:

* `RightDerived.Comparison` for degree functors and the degree-zero comparison
  attached to an arbitrary bounded-below right-derived model, and
  `RightDerived.Comparison.Naturality` for the natural isomorphism between its
  localization and canonical-single presentations;
* `RightDerived.Canonical` for the standard total-derived functor, its
  localization unit, and its degree-zero comparison;
* `RightDerived.Naturality` and `RightDerived.Naturality.Iso` for the action
  of natural transformations and natural isomorphisms on the standard
  total-derived functor;
* `RightDerived.Degree.Naturality` for degreewise functoriality of arbitrary
  models, and `RightDerived.Naturality.Degree` for its canonical specialization
  and compatibility with `F ⟶ R⁰F`; `RightDerived.Degree.InjectiveResolution`
  supplies the concrete bounded-to-ordinary degree isomorphism for a chosen
  injective-resolution model;
* `RightDerived.Cochain` and `RightDerived.Cochain.Naturality` for canonical
  maps into derived values and their compatibility with functoriality;
* `RightDerived.DeltaFunctor` for the pretriangulated and cohomological delta
  functors, with `DeltaFunctor.Naturality{/Iso}` acting on maps and
  isomorphisms of chosen models, `DeltaFunctor.{Connecting,Sequence}` exposing
  connecting maps and exact windows directly in terms of `RⁿF`, and
  `DeltaFunctor.Sequence.{Naturality,Functoriality}` for their action on maps
  of short exact complexes; `DeltaFunctor.Sequence.Augmented` supplies the
  standard low-degree sequence beginning with the zero object, and its
  `Naturality` and `Functoriality` leaves expose direct `R⁰/R¹` maps and the
  corresponding short-exact-complex functor;
* `RightDerived.Properties` for degree bounds and the degree-zero exactness
  criterion;
* `RightDerived.Universality` for acyclicity-based universality criteria,
  including the `HasMonoEmbedding` and canonical-model interfaces;
* `RightDerived.Value` for the value functor, its object and morphism
  projections, and their identity/composition computation laws, parameterized
  by a chosen localization model; `RightDerived.Value.Naturality` gives its
  action on transformations of functors on the homotopy category, and its
  `Iso` leaf gives the corresponding natural-isomorphism API;
* `RightDerived.PointwiseValue` for the bounded-below value functor assembled
  directly from pointwise right-derived values, without choosing a localization
  model or a total derived functor;
* `RightDerived.Cohomology` for the cohomology functor, its object/map
  computations, and cochain-map identity/composition laws; and
  `RightDerived.Cohomology.Naturality` for transformations between additive
  input functors, with its `Iso` leaf supplying natural isomorphisms.

The hierarchy keeps the construction independent of Chapter 13 while allowing
downstream developments to import this single public façade.
-/
