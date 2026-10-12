/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.QuasiFinite.Factorization
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Finite.Topology

/-!
# Topological consequences of quasi-finite morphisms

This file records the behavior of nowhere dense closed subsets under quasi-finite morphisms of
schemes.
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.Hom.QuasiFinite

/-- The image of a closed nowhere dense subset under a quasi-finite morphism of schemes is
nowhere dense. -/
theorem isNowhereDense_image_of_isClosed
    {X Y : Scheme.{u}} (f : Y ⟶ X) [Scheme.Hom.QuasiFinite f] (T : Set Y)
    (hT_closed : IsClosed T) (hT_nowhere : IsNowhereDense T) :
    IsNowhereDense (f '' T) := sorry

end AlgebraicGeometry.Scheme.Hom.QuasiFinite
