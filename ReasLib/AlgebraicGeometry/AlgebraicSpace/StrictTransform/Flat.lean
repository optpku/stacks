/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.StrictTransform
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Blowup
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Flat
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.FlatOver.BaseChange

/-!
# Flatness and strict transforms

Flatness along the blowup center makes the canonical strict-transform inclusion
and the canonical module quotient isomorphisms.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- If an algebraic space is flat over the base at all points over the blowup
center, its canonical strict-transform inclusion into the base change is an
isomorphism. -/
theorem strictTransform_ι_isIso_of_flatAt_over_center
    {S : Scheme.{u}} {B B' X : AlgebraicSpace S}
    (Z : ClosedSubspace B) (b : B' ⟶ B) [IsBlowup b Z] (f : X ⟶ B)
    [QuasiCompact (strictTransformOpenComplement b (Z.inverseImageSubspace b) f).ι]
    (hflat : ∀ x : Points X, Points.map f x ∈ Z.pointsSet → FlatAt f x) :
    IsIso (strictTransform b (Z.inverseImageSubspace b) f).ι :=
  sorry

/-- If a quasi-coherent module is flat over the base at all points over the
blowup center, the canonical quotient from its pullback to its strict transform
is an isomorphism. -/
theorem strictTransformπ_isIso_of_flatOverAt_over_center
    {S : Scheme.{u}} {B B' X : AlgebraicSpace S}
    (Z : ClosedSubspace B) (b : B' ⟶ B) [IsBlowup b Z] (f : X ⟶ B)
    (F : X.Modules) [F.IsQuasicoherent]
    (hflat : ∀ x : Points X, Points.map f x ∈ Z.pointsSet →
      Modules.flatOverAt F f x) :
    IsIso (strictTransformπ b (Z.inverseImageSubspace b) f F) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
