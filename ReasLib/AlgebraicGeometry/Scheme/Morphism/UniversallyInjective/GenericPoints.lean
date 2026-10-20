/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyInjective
public import Mathlib.Topology.Sober

/-!
# Universal Injectivity from Generic Points

This module gives a criterion for universal injectivity in terms of the generic
points of irreducible components and their residue fields.
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.UniversallyInjective

/-- A flat separated morphism which induces residue-field isomorphisms at the
generic points of its source and is injective on those generic points is
universally injective. -/
theorem of_flat_of_isSeparated_of_genericPoints {X Y : Scheme.{u}} (f : X ⟶ Y)
    [Flat f] [IsSeparated f]
    (hκ : ∀ ξ : X, ξ ∈ genericPoints X → IsIso (f.residueFieldMap ξ))
    (hgen : Set.InjOn f.base (genericPoints X)) :
    UniversallyInjective f := sorry

end AlgebraicGeometry.UniversallyInjective
