/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ResidueField
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FieldFiber
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.AffineSpace

/-!
# Affine-space fibres of morphisms of algebraic spaces

A morphism of algebraic spaces has affine-space fibre of dimension `r` at a
point `y` when the field-valued fibre over `Spec(κ(y))` is isomorphic, over
`κ(y)`, to affine `r`-space.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace Limits

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

namespace Hom

/-- A morphism `f : X ⟶ Y` has affine-space fibre of dimension `r` at `y` if
the field-valued fibre `X_y` is isomorphic over `κ(y)` to affine `r`-space. -/
def IsAffineSpaceFiber {S : Scheme.{u}} {X Y : AlgebraicSpace S} [IsDecent Y]
    (f : X ⟶ Y) (r : ℕ) (y : Points Y) : Prop :=
  Nonempty
    (Over.mk (fieldFiberToSpec f (FieldValuedPoint.residuePoint y)) ≅
      Over.mk
        (AffineSpace.toBase (ULift.{u} (Fin r))
          (ofOver (FieldValuedPoint.residuePoint y).overObj)))

/-- Affine-space fibres are Over-isomorphisms to affine `r`-space over
`Spec(κ(y))`. -/
theorem isAffineSpaceFiber_iff {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    [IsDecent Y] (f : X ⟶ Y) (r : ℕ) (y : Points Y) :
    IsAffineSpaceFiber f r y ↔
      Nonempty
        (Over.mk (fieldFiberToSpec f (FieldValuedPoint.residuePoint y)) ≅
          Over.mk
            (AffineSpace.toBase (ULift.{u} (Fin r))
              (ofOver (FieldValuedPoint.residuePoint y).overObj))) :=
  Iff.rfl

end Hom

end AlgebraicGeometry.AlgebraicSpace
