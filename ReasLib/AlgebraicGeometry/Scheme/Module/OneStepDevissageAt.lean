/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.OneStepDevissage
public import ReasLib.FieldTheory.Transcendence.PurelyTranscendental
public import ReasLib.Topology.KrullDimension.Local

/-!
# One-step dévissages at a point

This module refines a chosen one-step dévissage over the image of a point by the
support and distinguished-point conditions at that point.
-/

@[expose] public section

open CategoryTheory
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

/-- The chosen data and properties of a one-step dévissage of `ℱ / X / S` at `x`. -/
structure OneStepDevissageAt {S : Scheme.{u}} (X : Over S) (ℱ : X.left.Modules)
    [LocallyOfFiniteType X.hom] [ℱ.IsQuasicoherent] [ℱ.IsFiniteType] (x : X.left) where
  /-- The underlying one-step dévissage over the image `X.hom x`. -/
  toOneStepDevissage : OneStepDevissage X ℱ (X.hom x)
  /-- The point of the fibre support corresponding to `x`. -/
  supportPoint :
    moduleSupport ((Scheme.Modules.pullback (X.hom.fiberι (X.hom x))).obj ℱ)
  /-- The chosen support point has underlying fibre point `X.hom.asFiber x`. -/
  supportPoint_eq : (supportPoint : X.hom.fiber (X.hom x)) = X.hom.asFiber x
  /-- The support dimension at `x` is maximal in the fibre support. -/
  maximalSupportDimension :
    topologicalKrullDimAt supportPoint = fiberSupportDimension X.hom ℱ (X.hom x)
  /-- The distinguished point of the auxiliary scheme. -/
  z : toOneStepDevissage.Z.left
  /-- The distinguished point of the smooth model. -/
  y : toOneStepDevissage.Y.left
  /-- The distinguished point of the auxiliary scheme maps to `x`. -/
  i_z : toOneStepDevissage.i.left z = x
  /-- The distinguished point of the auxiliary scheme maps to `y`. -/
  π_z : toOneStepDevissage.π.left z = y
  /-- The fibre of `π` over `y` consists only of `z`. -/
  distinguishedFiber : toOneStepDevissage.π.left ⁻¹' {y} = {z}
  /-- The distinguished point `y` lies over `X.hom x`. -/
  basePoint : toOneStepDevissage.Y.hom y = X.hom x
  /-- The residue-field extension `κ(y) / κ(X.hom x)` is purely transcendental. -/
  residueExtension :
    ((S.residueFieldCongr basePoint).inv ≫
      toOneStepDevissage.Y.hom.residueFieldMap y).hom.IsPurelyTranscendental

namespace OneStepDevissageAt

variable {S : Scheme.{u}} {X : Over S} {ℱ : X.left.Modules}
  [LocallyOfFiniteType X.hom] [ℱ.IsQuasicoherent] [ℱ.IsFiniteType] {x : X.left}

/-- Refine a one-step dévissage over `X.hom x` by the support and distinguished-point
conditions at `x`. -/
def ofDiagram
    (toOneStepDevissage : OneStepDevissage X ℱ (X.hom x))
    (supportPoint : moduleSupport ((Scheme.Modules.pullback (X.hom.fiberι (X.hom x))).obj ℱ))
    (z : toOneStepDevissage.Z.left) (y : toOneStepDevissage.Y.left)
    (supportPoint_eq : (supportPoint : X.hom.fiber (X.hom x)) = X.hom.asFiber x)
    (maximalSupportDimension :
      topologicalKrullDimAt supportPoint = fiberSupportDimension X.hom ℱ (X.hom x))
    (i_z : toOneStepDevissage.i.left z = x)
    (π_z : toOneStepDevissage.π.left z = y)
    (distinguishedFiber : toOneStepDevissage.π.left ⁻¹' {y} = {z})
    (basePoint : toOneStepDevissage.Y.hom y = X.hom x)
    (residueExtension :
      ((S.residueFieldCongr basePoint).inv ≫
        toOneStepDevissage.Y.hom.residueFieldMap y).hom.IsPurelyTranscendental) :
    OneStepDevissageAt X ℱ x where
  toOneStepDevissage := toOneStepDevissage
  supportPoint := supportPoint
  supportPoint_eq := supportPoint_eq
  maximalSupportDimension := maximalSupportDimension
  z := z
  y := y
  i_z := i_z
  π_z := π_z
  distinguishedFiber := distinguishedFiber
  basePoint := basePoint
  residueExtension := residueExtension

/-- Reconstructing a one-step dévissage at `x` from all of its fields returns the
original chosen dévissage. -/
theorem ofDiagram_self (D : OneStepDevissageAt X ℱ x) :
    ofDiagram D.toOneStepDevissage D.supportPoint D.z D.y D.supportPoint_eq
      D.maximalSupportDimension D.i_z D.π_z D.distinguishedFiber D.basePoint
      D.residueExtension = D := sorry

/-- The distinguished support point realizes the full dimension of the fibre support. -/
theorem maximalSupportDimension_eq (D : OneStepDevissageAt X ℱ x) :
    topologicalKrullDimAt D.supportPoint =
      fiberSupportDimension X.hom ℱ (X.hom x) := sorry

/-- The two distinguished-point equations in a one-step dévissage at `x`. -/
theorem mapsDistinguishedPoint (D : OneStepDevissageAt X ℱ x) :
    D.toOneStepDevissage.i.left D.z = x ∧
      D.toOneStepDevissage.π.left D.z = D.y := sorry

/-- The fibre of the finite map over the distinguished point is a singleton. -/
theorem distinguishedFiber_eq (D : OneStepDevissageAt X ℱ x) :
    D.toOneStepDevissage.π.left ⁻¹' {D.y} = {D.z} := sorry

/-- The residue-field extension at the distinguished point is purely transcendental. -/
theorem residueExtension_isPurelyTranscendental (D : OneStepDevissageAt X ℱ x) :
    ((S.residueFieldCongr D.basePoint).inv ≫
      D.toOneStepDevissage.Y.hom.residueFieldMap D.y).hom.IsPurelyTranscendental := sorry

end OneStepDevissageAt

end AlgebraicGeometry.Scheme.Modules
