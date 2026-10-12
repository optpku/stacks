/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Fibered.Stack.Basic
public import ReasLib.CategoryTheory.Fibered.Stack.LocalEquivalence
public import ReasLib.CategoryTheory.Fibered.Stack.InGroupoids
public import ReasLib.CategoryTheory.Fibered.Stack.InSetoids
public import ReasLib.CategoryTheory.Fibered.Stack.InSetoids.FiberIsoClassPresheaf
public import ReasLib.CategoryTheory.Fibered.Stack.CategoryOfElements
public import ReasLib.CategoryTheory.Fibered.Stack.Over
public import ReasLib.CategoryTheory.Fibered.Stack.Over.Equivalence
public import ReasLib.CategoryTheory.Fibered.Stack.Slice
public import ReasLib.CategoryTheory.Fibered.Stack.Hom
public import ReasLib.CategoryTheory.Fibered.Stack.Pullback
public import ReasLib.CategoryTheory.Fibered.Stack.Prestack
public import ReasLib.CategoryTheory.Fibered.Stack.InGroupoidsOver
public import ReasLib.CategoryTheory.Fibered.Stack.InGroupoidsOver.Forgetful
public import ReasLib.CategoryTheory.Fibered.Stack.InGroupoidsOver.Equivalence
public import ReasLib.CategoryTheory.Fibered.Stack.InGroupoidsOver.Local
public import ReasLib.CategoryTheory.Fibered.Stack.InGroupoidsOver.Pullback
public import ReasLib.CategoryTheory.Fibered.Stack.InGroupoidsOver.Stackification
public import ReasLib.CategoryTheory.Fibered.Stack.InGroupoidsOver.Criterion
public import ReasLib.CategoryTheory.Fibered.Stack.InSetoidsOver
public import ReasLib.CategoryTheory.Fibered.Stack.InSetoidsOver.Forgetful
public import ReasLib.CategoryTheory.Fibered.Stack.InSetoidsOver.Equivalence
public import ReasLib.CategoryTheory.Fibered.Stack.InSetsOver
public import ReasLib.CategoryTheory.Fibered.Stack.InSetsOver.Forgetful
public import ReasLib.CategoryTheory.Fibered.Stack.InSetsOver.Equivalence
public import ReasLib.CategoryTheory.Fibered.Stack.InSetsOver.Iso
public import ReasLib.CategoryTheory.Fibered.Stack.InSetsOver.Restriction
public import ReasLib.CategoryTheory.Fibered.Stack.InSetoidsOver.TwoFibreProduct
public import ReasLib.CategoryTheory.Fibered.Stack.InSetsOver.TwoFibreProduct
public import ReasLib.CategoryTheory.Fibered.Stack.InGroupoidsOver.InheritedTopology
public import ReasLib.CategoryTheory.Fibered.CartesianBasedFunctor.DescentData.Cover
public import ReasLib.CategoryTheory.Fibered.Pullback
public import ReasLib.CategoryTheory.Fibered.CategoricalPullback.Stack
public import ReasLib.CategoryTheory.Fibered.InheritedTopology
public import ReasLib.CategoryTheory.Fibered.InheritedTopology.InGroupoids
public import ReasLib.CategoryTheory.Fibered.InheritedTopology.Over
public import ReasLib.CategoryTheory.Fibered.Stack.InheritedTopology.Composition
public import ReasLib.CategoryTheory.Fibered.InheritedTopology.Morphism
public import ReasLib.CategoryTheory.Fibered.CategoryOver.InheritedTopology
public import ReasLib.CategoryTheory.Fibered.Stack.Stackification
public import ReasLib.CategoryTheory.Fibered.Stack.Stackification.Existence
public import ReasLib.CategoryTheory.Fibered.Stack.Stackification.LocalEquivalence
public import ReasLib.CategoryTheory.Fibered.Stack.Stackification.TwoFibreProduct
public import ReasLib.CategoryTheory.Fibered.Stack.Over.TwoFibreProduct
public import ReasLib.CategoryTheory.Fibered.Stack.Equivalence
public import ReasLib.CategoryTheory.Fibered.Stack.Inertia
public import ReasLib.CategoryTheory.Fibered.Inertia.Stackification
public import ReasLib.CategoryTheory.Fibered.Stack.Refinement
public import ReasLib.CategoryTheory.Fibered.Stack.TwoFibreProduct
public import ReasLib.CategoryTheory.Fibered.Groupoids.TwoFibreProduct.Stackification
public import ReasLib.CategoryTheory.Fibered.Stack.Coverwise
public import ReasLib.CategoryTheory.Fibered.Stack.StronglyCartesianSubcategory
public import ReasLib.CategoryTheory.Fibered.Pushforward
public import ReasLib.CategoryTheory.Fibered.Pushforward.Cartesian
public import ReasLib.CategoryTheory.Fibered.Pushforward.Equivalence
public import ReasLib.CategoryTheory.Fibered.Pushforward.InGroupoids
public import ReasLib.CategoryTheory.Fibered.Pushforward.Map
public import ReasLib.CategoryTheory.Fibered.Pushforward.Map.Fibered
public import ReasLib.CategoryTheory.Fibered.Pushforward.SourcePrecomposition
public import ReasLib.CategoryTheory.Fibered.Pushforward.Unit
public import ReasLib.CategoryTheory.Fibered.Pushforward.Hom
public import ReasLib.CategoryTheory.Fibered.Stack.InverseImage
public import ReasLib.CategoryTheory.Fibered.Stack.InverseImage.Hom
public import ReasLib.CategoryTheory.Fibered.Stack.InverseImage.Existence
public import ReasLib.CategoryTheory.Fibered.Stack.InverseImage.Stackification
public import ReasLib.CategoryTheory.Fibered.Stack.InverseImage.Comparison

/-!
# Stack infrastructure — aggregate

This module re-exports the complete stack hierarchy: basic stack condition, stacks in groupoids,
stacks in setoids/sets, prestacks, the bundled 2-categories, morphism API, pullback, inherited
topology, stackification, equivalence transfer, refinement independence, inverse-image existence
and comparison, and two-fibre products. Experimental descent-completion
construction data remain in their leaf module until they acquire a complete categorical owner.
-/
