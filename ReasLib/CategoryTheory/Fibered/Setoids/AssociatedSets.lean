/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Fibered.FiberIsoClassPresheaf
public import ReasLib.CategoryTheory.Fibered.Setoids.Equivalence
public import ReasLib.CategoryTheory.Fibered.Setoids.AssociatedSets.Basic
public import ReasLib.CategoryTheory.Fibered.Setoids.AssociatedSets.Comparison
public import ReasLib.CategoryTheory.Fibered.Setoids.AssociatedSets.Naturality

/-!
# The associated discrete fibration of a category fibred in setoids

Compatibility aggregate for the associated-sets API.

* `Fibered.FiberIsoClassPresheaf` owns the fiberwise isomorphism-class
  presheaf and its functoriality.
* `Fibered.Setoids.Equivalence` provides equivalence-to-setoids criteria.
* `AssociatedSets.Basic` provides the associated discrete fibration and its
  fiberwise computation and naturality API.
* `AssociatedSets.Comparison` provides the explicit comparison with the
  setoid image and its quotient-level equivalence API.
* `AssociatedSets.Naturality` identifies the two comparison routes induced by
  a morphism, with explicit category-of-elements components.

New users may import the smallest leaf matching their dependency.
-/
