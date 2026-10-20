/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ValuativeCriterion
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Decent
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.UniversallyClosed
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.RelativeConditions
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ValuativeCriterion.UniversallyClosed

/-!
# Valuative criterion for universal closedness under decency

A quasi-compact morphism of algebraic spaces with decent source, or a
quasi-compact decent morphism, is universally closed if and only if it satisfies
the existence part of the valuative criterion.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

namespace UniversallyClosed

/-- A quasi-compact morphism of algebraic spaces over a scheme with decent source
is universally closed if and only if it satisfies the existence part of the
valuative criterion. -/
theorem iff_existence_of_isDecent {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) [QuasiCompact f] [IsDecent X] :
    UniversallyClosed f ↔ ValuativeCriterion.Existence f :=
  sorry

/-- A quasi-compact decent morphism of algebraic spaces over a scheme is
universally closed if and only if it satisfies the existence part of the
valuative criterion. -/
theorem iff_existence_of_decent {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) [QuasiCompact f] [Decent f] :
    UniversallyClosed f ↔ ValuativeCriterion.Existence f :=
  sorry

end UniversallyClosed

namespace ValuativeCriterion.Existence

/-- A quasi-compact universally closed morphism of algebraic spaces over a scheme
with decent source satisfies the existence part of the valuative criterion. -/
instance of_universallyClosed_of_isDecent {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) [QuasiCompact f] [IsDecent X] [UniversallyClosed f] : Existence f :=
  (UniversallyClosed.iff_existence_of_isDecent f).mp inferInstance

/-- A quasi-compact universally closed decent morphism of algebraic spaces over
a scheme satisfies the existence part of the valuative criterion. -/
instance of_universallyClosed_of_decent {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) [QuasiCompact f] [Decent f] [UniversallyClosed f] : Existence f :=
  (UniversallyClosed.iff_existence_of_decent f).mp inferInstance

end ValuativeCriterion.Existence

end AlgebraicGeometry.AlgebraicSpace
