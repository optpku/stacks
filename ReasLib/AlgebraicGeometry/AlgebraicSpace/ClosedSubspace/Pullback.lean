/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Closed.InverseImage
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ClosedSubspace.Ideal
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.IdealSubobject.Pullback
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Divisor.EffectiveCartier

/-!
# Inverse images of closed subspaces and defined pullbacks

The inverse image of a closed subspace is its fibre-product closed subspace.
Its pullback is defined when that inverse image is an effective Cartier divisor.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.ClosedSubspace

/-- The inclusion of an inverse image is the unbundled inverse-image immersion. -/
theorem inverseImage_ι {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (Z : ClosedSubspace X) (f : Y ⟶ X) :
    (Z.inverseImageSubspace f).ι =
      @inverseImageι S X Y Z.X f Z.ι Z.isClosedImmersion :=
  sorry

/-- An inverse-image closed subspace has the fibre-product inclusion, which is
a closed immersion. -/
theorem inverseImage_spec {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (Z : ClosedSubspace X) (f : Y ⟶ X) :
    (Z.inverseImageSubspace f).ι =
        @inverseImageι S X Y Z.X f Z.ι Z.isClosedImmersion ∧
      IsClosedImmersion (Z.inverseImageSubspace f).ι :=
  sorry

/-- The pullback of a closed subspace by `f` is defined when the inverse image is
an effective Cartier divisor. -/
abbrev pullbackDefined {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (Z : ClosedSubspace X) (f : Y ⟶ X) : Prop :=
  IsEffectiveCartierDivisor (Z.inverseImageSubspace f).ι

/-- Definedness of the pullback is effective Cartier-ness of the inverse image. -/
theorem pullbackDefined_iff {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (Z : ClosedSubspace X) (f : Y ⟶ X) :
    Z.pullbackDefined f ↔ IsEffectiveCartierDivisor (Z.inverseImageSubspace f).ι :=
  sorry

/-- The kernel ideal of an inverse image is the inverse-image ideal sheaf. -/
theorem inverseImage_idealSheaf {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (Z : ClosedSubspace X) (f : Y ⟶ X) :
    (Z.inverseImageSubspace f).idealSheaf = Z.idealSheaf.pullback f :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.ClosedSubspace
