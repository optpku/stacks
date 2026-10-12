/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.FiberSupportDimension.AmbientPoint
public import ReasLib.AlgebraicGeometry.Scheme.Module.OneStepDevissageAt

/-!
# One-step dévissages at ambient fibre points

This module packages a one-step dévissage with local-dimension and
distinguished-point conditions at an arbitrary point of the ambient fibre.
-/

@[expose] public section

open CategoryTheory
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

/-- A one-step dévissage at an ambient point `x`, with its distinguished points and
local-dimension condition. The point `x` need not be supplied with a membership witness
for the fibre support. -/
structure OneStepDevissageAtAmbientPoint {S : Scheme.{u}} (X : Over S)
    (F : X.left.Modules) [LocallyOfFiniteType X.hom] [F.IsQuasicoherent]
    [F.IsFiniteType] (x : X.left) where
  /-- The underlying one-step dévissage over the image `X.hom x`. -/
  toOneStepDevissage : OneStepDevissage X F (X.hom x)
  /-- The fibre support has maximal local dimension at the ambient point `x`. -/
  maximalSupportDimension :
    ambientFiberSupportDimensionAt X.hom F x = fiberSupportDimension X.hom F (X.hom x)
  /-- The distinguished point of the auxiliary scheme. -/
  z : toOneStepDevissage.Z.left
  /-- The distinguished point of the smooth model. -/
  y : toOneStepDevissage.Y.left
  /-- The distinguished point of the auxiliary scheme maps to `x`. -/
  i_z : toOneStepDevissage.i.left z = x
  /-- The distinguished point of the auxiliary scheme maps to `y`. -/
  π_z : toOneStepDevissage.π.left z = y
  /-- The fibre over `y` consists only of `z`. -/
  distinguishedFiber : toOneStepDevissage.π.left ⁻¹' {y} = {z}
  /-- The distinguished point `y` lies over `X.hom x`. -/
  basePoint : toOneStepDevissage.Y.hom y = X.hom x
  /-- The residue-field extension `κ(y) / κ(X.hom x)` is purely transcendental. -/
  residueExtension :
    let Y := toOneStepDevissage.Y
    ((S.residueFieldCongr basePoint).inv ≫ Y.hom.residueFieldMap y).hom.IsPurelyTranscendental

namespace OneStepDevissageAtAmbientPoint

variable {S : Scheme.{u}} {X : Over S} {F : X.left.Modules}
  [LocallyOfFiniteType X.hom] [F.IsQuasicoherent] [F.IsFiniteType] {x : X.left}

/-- Construct an ambient-point one-step dévissage from its diagram, distinguished
points, and defining properties. -/
def ofDiagram
    (toOneStepDevissage : OneStepDevissage X F (X.hom x))
    (maximalSupportDimension :
      ambientFiberSupportDimensionAt X.hom F x = fiberSupportDimension X.hom F (X.hom x))
    (z : toOneStepDevissage.Z.left) (y : toOneStepDevissage.Y.left)
    (i_z : toOneStepDevissage.i.left z = x)
    (π_z : toOneStepDevissage.π.left z = y)
    (distinguishedFiber : toOneStepDevissage.π.left ⁻¹' {y} = {z})
    (basePoint : toOneStepDevissage.Y.hom y = X.hom x)
    (residueExtension :
      let Y := toOneStepDevissage.Y
      ((S.residueFieldCongr basePoint).inv ≫
        Y.hom.residueFieldMap y).hom.IsPurelyTranscendental) :
    OneStepDevissageAtAmbientPoint X F x where
  toOneStepDevissage := toOneStepDevissage
  maximalSupportDimension := maximalSupportDimension
  z := z
  y := y
  i_z := i_z
  π_z := π_z
  distinguishedFiber := distinguishedFiber
  basePoint := basePoint
  residueExtension := residueExtension

/-- Reconstructing an ambient-point one-step dévissage from all of its fields returns
the original chosen dévissage. -/
theorem ofDiagram_self (D : OneStepDevissageAtAmbientPoint X F x) :
    ofDiagram D.toOneStepDevissage D.maximalSupportDimension D.z D.y D.i_z D.π_z
      D.distinguishedFiber D.basePoint D.residueExtension = D := sorry

/-- The ambient-point local dimension of the fibre support is its full fibre-support
dimension. -/
theorem maximalSupportDimension_eq (D : OneStepDevissageAtAmbientPoint X F x) :
    ambientFiberSupportDimensionAt X.hom F x =
      fiberSupportDimension X.hom F (X.hom x) := sorry

/-- The two maps from the distinguished auxiliary point have their prescribed values. -/
theorem mapsDistinguishedPoint (D : OneStepDevissageAtAmbientPoint X F x) :
    D.toOneStepDevissage.i.left D.z = x ∧
      D.toOneStepDevissage.π.left D.z = D.y := sorry

/-- The fibre of the finite map over the distinguished point is a singleton. -/
theorem distinguishedFiber_eq (D : OneStepDevissageAtAmbientPoint X F x) :
    D.toOneStepDevissage.π.left ⁻¹' {D.y} = {D.z} := sorry

/-- The residue-field extension at the distinguished point is purely transcendental. -/
theorem residueExtension_isPurelyTranscendental
    (D : OneStepDevissageAtAmbientPoint X F x) :
    ((S.residueFieldCongr D.basePoint).inv ≫
      D.toOneStepDevissage.Y.hom.residueFieldMap D.y).hom.IsPurelyTranscendental := sorry

/-- A support-point one-step dévissage satisfies the corresponding ambient-point
maximal-dimension condition. -/
theorem ofSupportPoint_maximalSupportDimension (D : OneStepDevissageAt X F x) :
    ambientFiberSupportDimensionAt X.hom F x =
      fiberSupportDimension X.hom F (X.hom x) := sorry

/-- Forget the chosen support witness in a support-point one-step dévissage. -/
def ofSupportPoint (D : OneStepDevissageAt X F x) :
    OneStepDevissageAtAmbientPoint X F x where
  toOneStepDevissage := D.toOneStepDevissage
  maximalSupportDimension := ofSupportPoint_maximalSupportDimension D
  z := D.z
  y := D.y
  i_z := D.i_z
  π_z := D.π_z
  distinguishedFiber := D.distinguishedFiber
  basePoint := D.basePoint
  residueExtension := D.residueExtension

end OneStepDevissageAtAmbientPoint

end AlgebraicGeometry.Scheme.Modules
