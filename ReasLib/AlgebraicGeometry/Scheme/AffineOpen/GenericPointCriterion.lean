/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.Topology.Sober

/-!
# Affine neighborhoods from generic points and stalk maps

An affine-neighborhood criterion for finite images under morphisms of schemes.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.Hom

/-- If a morphism from an affine scheme to a quasi-separated scheme is injective on generic
points, maps generic points to generic points, and induces stalk isomorphisms along a finite
subset, then the image of that subset is contained in an affine open. -/
theorem exists_affineOpen_containing_image_of_stalkMap_isIso
    {T X : Scheme.{u}} (f : T ⟶ X) [IsAffine T] [QuasiSeparatedSpace X]
    (hX0 : (genericPoints X).Finite)
    (hmap : Set.MapsTo f.base (genericPoints T) (genericPoints X))
    (hinj : Set.InjOn f.base (genericPoints T))
    (S : Set T) (hS : S.Finite)
    (hstalk : ∀ t : T, t ∈ S → IsIso (f.stalkMap t)) :
    ∃ U : X.affineOpens, Set.image f.base S ⊆ ((U : X.Opens) : Set X) := sorry

end AlgebraicGeometry.Scheme.Hom
