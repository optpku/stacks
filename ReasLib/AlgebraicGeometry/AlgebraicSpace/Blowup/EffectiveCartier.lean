/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Blowup.RelativeProj
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Divisor.EffectiveCartier
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.IdealSubobject.Product

/-!
# Blowups along effective Cartier divisors

The canonical morphism of a blowup along an effective Cartier divisor is an
isomorphism, and the blowup is isomorphic over its base to the identity morphism.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Blowup

/-- The canonical morphism of a blowup along an effective Cartier divisor is an
isomorphism. -/
theorem isIso_hom {S : Scheme.{u}} {X : AlgebraicSpace S}
    (Z : ClosedSubspace X) [IsEffectiveCartierDivisor Z.ι] (π : along Z) :
    IsIso π.hom :=
  sorry

/-- A chosen blowup of `X` along an effective Cartier divisor `Z` is isomorphic
over `X` to the identity morphism of `X`. -/
theorem isoOver_id {S : Scheme.{u}} {X : AlgebraicSpace S}
    (Z : ClosedSubspace X) [IsEffectiveCartierDivisor Z.ι] (π : along Z) :
    Nonempty (Over.mk π.hom ≅ Over.mk (𝟙 X)) :=
  sorry

/-- Multiplying the ideal of a closed subspace by the ideal of an effective
Cartier divisor does not change its blowup up to isomorphism over the base. -/
theorem isoOver_mul_effectiveCartier {S : Scheme.{u}} {B : AlgebraicSpace S}
    (Z D : ClosedSubspace B) [IsQuasiCoherent Z.idealSheaf]
    [IsEffectiveCartierDivisor D.ι] (π : along Z)
    (π' : along
      (ClosedSubspace.ofQuasiCoherentIdeal
        (IdealSubobject.mul Z.idealSheaf D.idealSheaf))) :
    Nonempty (Over.mk
      (alongHom
        (ClosedSubspace.ofQuasiCoherentIdeal
          (IdealSubobject.mul Z.idealSheaf D.idealSheaf)) π') ≅ Over.mk π.hom) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Blowup
