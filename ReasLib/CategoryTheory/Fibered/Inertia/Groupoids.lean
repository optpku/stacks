/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Fibered.Inertia.Groupoids.Closure
public import ReasLib.CategoryTheory.Fibered.Inertia.Groupoids.Objects
public import ReasLib.CategoryTheory.Fibered.Inertia.Groupoids.Functoriality
public import ReasLib.CategoryTheory.Fibered.Inertia.Groupoids.AbsolutePseudofunctor
public import ReasLib.CategoryTheory.Fibered.Inertia.Groupoids.AbsoluteTransformations
public import ReasLib.CategoryTheory.Fibered.Inertia.Groupoids.RelativeFunctoriality
public import ReasLib.CategoryTheory.Fibered.Inertia.Groupoids.FixedPseudoPullback

/-!
# Inertia of categories fibred in groupoids

Compatibility aggregate for the groupoid-fibred inertia API. The implementation is split by
responsibility into closure, object owners, absolute pseudofunctor and transformation APIs,
relative/square functoriality, and the fixed pseudo-pullback comparison.
-/

@[expose] public section
