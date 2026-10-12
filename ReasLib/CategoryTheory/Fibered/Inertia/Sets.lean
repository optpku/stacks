/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Fibered.Inertia.Sets.Closure
public import ReasLib.CategoryTheory.Fibered.Inertia.Sets.Objects
public import ReasLib.CategoryTheory.Fibered.Inertia.Sets.AbsolutePseudofunctor
public import ReasLib.CategoryTheory.Fibered.Inertia.Sets.Functoriality
public import ReasLib.CategoryTheory.Fibered.Inertia.Sets.AbsoluteTransformations
public import ReasLib.CategoryTheory.Fibered.Inertia.Sets.RelativeFunctoriality

/-!
# Inertia of categories fibred in sets

Compatibility aggregate for the set-fibred inertia API. The implementation is separated into
closure facts, bundled object owners, direct typed functoriality, absolute pseudofunctor and
strong-transformation APIs, and relative-inertia functoriality.

Import a leaf module when only one responsibility is required; use
`Sets.Functoriality` for the application-facing `map`/`map₂` owners and their
computations. This aggregate is the stable comprehensive entry point for users
of inertia in sets.
-/

@[expose] public section
