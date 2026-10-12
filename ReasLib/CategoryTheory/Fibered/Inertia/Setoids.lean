/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Fibered.Inertia.Setoids.Closure
public import ReasLib.CategoryTheory.Fibered.Inertia.Setoids.Objects
public import ReasLib.CategoryTheory.Fibered.Inertia.Setoids.Functoriality
public import ReasLib.CategoryTheory.Fibered.Inertia.Setoids.AbsolutePseudofunctor
public import ReasLib.CategoryTheory.Fibered.Inertia.Setoids.AbsoluteTransformations
public import ReasLib.CategoryTheory.Fibered.Inertia.Setoids.RelativeFunctoriality
public import ReasLib.CategoryTheory.Fibered.Inertia.Setoids.GroupoidCompatibility

/-!
# Inertia of categories fibred in setoids

Compatibility aggregate for the setoid-fibred inertia API. The implementation
is separated into closure facts, bundled object owners, absolute pseudofunctor
and strong-transformation APIs, relative-inertia functoriality, local hom
actions, and compatibility with the encompassing groupoid owner.

Import a leaf module when only one responsibility is required; this aggregate
remains the stable comprehensive entry point for existing users.
-/

@[expose] public section
