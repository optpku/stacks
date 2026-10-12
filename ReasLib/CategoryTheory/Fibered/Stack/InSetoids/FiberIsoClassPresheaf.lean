/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Fibered.Stack.InSetoids.FiberIsoClassPresheaf.Criterion
public import ReasLib.CategoryTheory.Fibered.Stack.InSetoids.AssociatedSets.Pseudofunctor
public import ReasLib.CategoryTheory.Fibered.Stack.InSetoids.AssociatedSets.Comparison

/-!
# Stacks in setoids and fibrewise isomorphism classes

Compatibility aggregate for the historical `FiberIsoClassPresheaf` import.  The declarations are
owned by focused leaves:

* `FiberIsoClassPresheaf.Criterion` owns the sheaf criterion;
* `AssociatedSets.Basic` owns the bundled associated stack and represented maps;
* `AssociatedSets.Functor` owns the homotopy-category functor;
* `AssociatedSets.Pseudofunctor` owns the bicategorical quotient and coherence readouts;
* `AssociatedSets.Comparison` owns the canonical comparison and its bundled naturality.

Existing imports of this module continue to expose the complete public API, while direct users can
now import only the layer they need.
-/
