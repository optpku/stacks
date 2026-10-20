/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.IsoOverOpen.BaseChange
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Etale
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Separation
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Closed.InverseImage

/-! # Étale excision for morphisms that are isomorphisms over an open -/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

namespace IsoOverOpen

/-- A separated étale morphism of algebraic spaces that is an isomorphism over a closed
subspace induces an equivalence, by base change, between the categories of morphisms
that are isomorphisms over the complementary open and its inverse image. -/
@[stacks 0BGY, instance]
instance baseChange_isEquivalence {S : Scheme.{u}}
    {V W T : AlgebraicSpace S} (f : V ⟶ W) [Etale f] [Separated f]
    (i : T ⟶ W) [IsClosedImmersion i] [IsIso (inverseImageTo f i)] :
    (baseChange f (closedImmersionComplementι i)).IsEquivalence :=
  sorry

end IsoOverOpen

end AlgebraicGeometry.AlgebraicSpace
