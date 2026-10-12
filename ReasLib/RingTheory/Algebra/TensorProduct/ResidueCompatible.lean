/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.Algebra.TensorProduct.RingHom
public import ReasLib.RingTheory.RingHom.Local.Residue

@[expose] public section

/-!
# Tensor products of residue-compatible local maps

A coherent square of explicit residue-compatible local algebra maps has an
underlying commutative square of ring homomorphisms.  The neutral
`Algebra.TensorProduct.RingHom.Square` API owns its tensor product, inclusions,
induced map, and equivalence independently of strict henselizations,
localization at primes, or any chosen geometric residue field.

The square stores only its four boundary comparisons.  Its diagonal comparison
and all comparison-dependent algebra structures are derived deterministically
from those boundary maps and their coherence.
-/

universe u v w x y z t

namespace Algebra.TensorProduct.ResidueCompatible

section

variable {R : Type u} {S : Type v} {T : Type w}
variable {X : Type x} {Y : Type y} {Z : Type z} {W : Type t}
variable [CommRing R] [CommRing S] [CommRing T]
variable [CommRing X] [CommRing Y] [CommRing Z] [CommRing W]
variable [Algebra R S] [Algebra R T]
variable [Algebra R X] [Algebra R Y] [Algebra R Z] [Algebra R W]
variable [Algebra S Y] [Algebra S W]
variable [Algebra T Z] [Algebra T W]
variable [IsScalarTower R S Y] [IsScalarTower R S W]
variable [IsScalarTower R T Z] [IsScalarTower R T W]
variable [IsLocalRing X] [IsLocalRing Y] [IsLocalRing Z] [IsLocalRing W]

/-- A commutative square of explicit residue-compatible local algebra maps.
The two lower edges are kept over their native scalar rings; the `comm` field
compares their underlying ring homomorphisms without choosing an additional
common scalar presentation. -/
@[stacks 0GIP "residue-compatible square of local algebra maps"]
structure Square where
  /-- The prescribed residue-field map on the edge `X → Y`. -/
  residueSourceLeft : IsLocalRing.ResidueField X →+* IsLocalRing.ResidueField Y
  /-- The local comparison map on the edge `X → Y`. -/
  sourceLeft : AlgHom.Local.ResidueCompatible (R := R) (A := X) (B := Y) residueSourceLeft
  /-- The prescribed residue-field map on the edge `X → Z`. -/
  residueSourceRight : IsLocalRing.ResidueField X →+* IsLocalRing.ResidueField Z
  /-- The local comparison map on the edge `X → Z`. -/
  sourceRight : AlgHom.Local.ResidueCompatible (R := R) (A := X) (B := Z) residueSourceRight
  /-- The prescribed residue-field map on the edge `Y → W`. -/
  residueLeftTarget : IsLocalRing.ResidueField Y →+* IsLocalRing.ResidueField W
  /-- The local comparison map on the edge `Y → W`, over `S`. -/
  leftTarget : AlgHom.Local.ResidueCompatible (R := S) (A := Y) (B := W) residueLeftTarget
  /-- The prescribed residue-field map on the edge `Z → W`. -/
  residueRightTarget : IsLocalRing.ResidueField Z →+* IsLocalRing.ResidueField W
  /-- The local comparison map on the edge `Z → W`, over `T`. -/
  rightTarget : AlgHom.Local.ResidueCompatible (R := T) (A := Z) (B := W) residueRightTarget
  /-- The two routes from `X` to `W` agree as underlying ring homomorphisms.
This is stated before any scalar restriction, so the square does not require a
chosen presentation of the two lower paths over `R`. -/
  comm :
    leftTarget.toLocal.hom.toRingHom.comp sourceLeft.toLocal.hom.toRingHom =
      rightTarget.toLocal.hom.toRingHom.comp sourceRight.toLocal.hom.toRingHom

namespace Square

/-- Forget the local and residue-field compatibility data of a coherent square,
retaining its underlying commutative square of ring homomorphisms.  This is the
bridge to the neutral `Algebra.TensorProduct.RingHom.Square` API for consumers
which only need the induced tensor-product ring map. -/
@[stacks 0GIP "underlying ring square of a residue-compatible square"]
def toRingHomSquare
    (square : Square (R := R) (S := S) (T := T) (X := X) (Y := Y) (Z := Z) (W := W)) :
    Algebra.TensorProduct.RingHom.Square (X := X) (Y := Y) (Z := Z) (W := W) where
  sourceLeft := square.sourceLeft.toLocal.hom.toRingHom
  sourceRight := square.sourceRight.toLocal.hom.toRingHom
  leftTarget := square.leftTarget.toLocal.hom.toRingHom
  rightTarget := square.rightTarget.toLocal.hom.toRingHom
  comm := square.comm

/-- The diagonal residue-compatible comparison from `X` to `W`, defined by the
`X → Y → W` route of a coherent square.  The other route agrees after the
respective residue maps are identified by `Square.residueFieldMaps_comm`. -/
def diagonal (square : Square (R := R) (S := S) (T := T) (X := X) (Y := Y) (Z := Z) (W := W)) :
    AlgHom.Local.ResidueCompatible (R := R) (A := X) (B := W)
      (square.residueLeftTarget.comp square.residueSourceLeft) :=
  (square.leftTarget.restrictScalars (R := R)).comp square.sourceLeft

/-- The explicit local map underlying the derived diagonal is the left route
of the coherent square after scalar restriction. -/
@[simp]
theorem diagonal_toLocal
    (square : Square (R := R) (S := S) (T := T) (X := X) (Y := Y) (Z := Z) (W := W)) :
    square.diagonal.toLocal =
      (square.leftTarget.toLocal.restrictScalars (R := R)).comp square.sourceLeft.toLocal := sorry

/-- The residue-field map of the derived diagonal is the composite of the
prescribed residue-field maps on its two defining edges. -/
@[simp]
theorem diagonal_residueFieldMap
    (square : Square (R := R) (S := S) (T := T) (X := X) (Y := Y) (Z := Z) (W := W)) :
    square.diagonal.toLocal.residueFieldMap = square.residueLeftTarget.comp square.residueSourceLeft := sorry

/-- The two prescribed residue-field composites in a coherent square agree.
This is derived from the equality of the explicit local composites, rather
than imposed as a second coherence field. -/
theorem residueFieldMaps_comm
    (square : Square (R := R) (S := S) (T := T) (X := X) (Y := Y) (Z := Z) (W := W)) :
    square.residueLeftTarget.comp square.residueSourceLeft = square.residueRightTarget.comp square.residueSourceRight := sorry

/-- The diagonal local comparison may equivalently be computed through the
`X → Z → W` route. -/
theorem diagonal_eq_right
    (square : Square (R := R) (S := S) (T := T) (X := X) (Y := Y) (Z := Z) (W := W)) :
    square.diagonal.toLocal =
      (square.rightTarget.toLocal.restrictScalars (R := R)).comp square.sourceRight.toLocal := sorry

end Square

end

end Algebra.TensorProduct.ResidueCompatible
