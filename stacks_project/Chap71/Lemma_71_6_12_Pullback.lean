/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ClosedSubspace.Pullback

/-!
# Inverse images of closed subspaces and defined pullbacks of Cartier divisors

The inverse image of a closed subspace along a morphism of algebraic spaces is
the fibre-product closed subspace, and the pullback of an effective Cartier
divisor is defined when that inverse image is itself effective Cartier.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

namespace ClosedSubspace

/-- The inverse image of a closed subspace along a morphism of algebraic spaces. -/
noncomputable abbrev inverseImage {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (Z : ClosedSubspace X) (f : Y ⟶ X) : ClosedSubspace Y :=
  Z.inverseImageSubspace f

#check (AlgebraicGeometry.AlgebraicSpace.ClosedSubspace.inverseImage_ι :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S}
      (Z : ClosedSubspace X) (f : Y ⟶ X),
      (Z.inverseImage f).ι = @inverseImageι S X Y Z.X f Z.ι Z.isClosedImmersion)

#check (AlgebraicGeometry.AlgebraicSpace.ClosedSubspace.inverseImage_spec :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S}
      (Z : ClosedSubspace X) (f : Y ⟶ X),
      (Z.inverseImage f).ι = @inverseImageι S X Y Z.X f Z.ι Z.isClosedImmersion ∧
        IsClosedImmersion (Z.inverseImage f).ι)

#check (AlgebraicGeometry.AlgebraicSpace.ClosedSubspace.pullbackDefined :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S}
      (Z : ClosedSubspace X) (f : Y ⟶ X), Prop)

#check (AlgebraicGeometry.AlgebraicSpace.ClosedSubspace.pullbackDefined_iff :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S}
      (Z : ClosedSubspace X) (f : Y ⟶ X),
      Z.pullbackDefined f ↔ IsEffectiveCartierDivisor (Z.inverseImage f).ι)

#check (AlgebraicGeometry.AlgebraicSpace.ClosedSubspace.inverseImage_idealSheaf :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S}
      (Z : ClosedSubspace X) (f : Y ⟶ X),
      (Z.inverseImage f).idealSheaf = Z.idealSheaf.pullback f)

end ClosedSubspace

end AlgebraicGeometry.AlgebraicSpace
