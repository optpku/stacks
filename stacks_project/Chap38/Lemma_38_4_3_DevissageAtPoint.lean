/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import stacks_project.Chap38.Definition_38_4_2_Devissage

/-!
# One-step dévissages at ambient fibre points

This file extends the support-point API for one-step dévissages to arbitrary ambient
points of a fibre.
-/

@[expose] public section

open CategoryTheory TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

/-- The local dimension at `x` of the support of `F` on the fibre of `f` through `x`.
The neighbourhoods are taken in the ambient fibre, so this is defined even when `x` is not
in the support. -/
def fiberSupportDimensionAt {X S : Scheme.{u}} (f : X ⟶ S)
    (F : X.Modules) (x : X) : WithBot ℕ∞ :=
  ⨅ U : OpenNhdsOf (f.asFiber x),
    topologicalKrullDim
      (Set.inter (U : Set (f.fiber (f x)))
        (moduleSupport ((pullback (f.fiberι (f x))).obj F)))

/-- `fiberSupportDimensionAt f F x` is computed from intersections of the fibre support with
ambient open neighbourhoods of `x`. -/
theorem fiberSupportDimensionAt_def {X S : Scheme.{u}} (f : X ⟶ S)
    (F : X.Modules) (x : X) :
    fiberSupportDimensionAt f F x =
      ⨅ U : OpenNhdsOf (f.asFiber x),
        topologicalKrullDim
          (Set.inter (U : Set (f.fiber (f x)))
            (moduleSupport ((pullback (f.fiberι (f x))).obj F))) := sorry

/-- At a point of the fibre support, the ambient-point support dimension agrees with the
local dimension of the corresponding support point. -/
theorem fiberSupportDimensionAt_eq_topologicalKrullDimAt {X S : Scheme.{u}}
    (f : X ⟶ S) (F : X.Modules) (x : X)
    (supportPoint : moduleSupport ((pullback (f.fiberι (f x))).obj F))
    (supportPoint_eq : (supportPoint : f.fiber (f x)) = f.asFiber x) :
    fiberSupportDimensionAt f F x = topologicalKrullDimAt supportPoint := sorry

/-- A one-step dévissage at an ambient point of a fibre, including the distinguished-point
data and the local-dimension condition without requiring the point to lie in the support. -/
structure OneStepDevissageAtPoint {S : Scheme.{u}} (X : Over S) (F : X.left.Modules)
    [LocallyOfFiniteType X.hom] [F.IsQuasicoherent] [F.IsFiniteType] (x : X.left) where
  /-- The underlying one-step dévissage over `X.hom x`. -/
  toOneStepDevissage : OneStepDevissage X F (X.hom x)
  /-- The support has maximal local dimension at the ambient fibre point `x`. -/
  maximalSupportDimension :
    fiberSupportDimensionAt X.hom F x = fiberSupportDimension X.hom F (X.hom x)
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
    let Y := toOneStepDevissage.Y
    ((S.residueFieldCongr basePoint).inv ≫ Y.hom.residueFieldMap y).hom.IsPurelyTranscendental

namespace OneStepDevissageAtPoint

variable {S : Scheme.{u}} {X : Over S} {F : X.left.Modules}
  [LocallyOfFiniteType X.hom] [F.IsQuasicoherent] [F.IsFiniteType] {x : X.left}

/-- Construct a one-step dévissage at an ambient fibre point from its diagram and defining
properties. -/
def ofDiagram
    (toOneStepDevissage : OneStepDevissage X F (X.hom x))
    (maximalSupportDimension :
      fiberSupportDimensionAt X.hom F x = fiberSupportDimension X.hom F (X.hom x))
    (z : toOneStepDevissage.Z.left) (y : toOneStepDevissage.Y.left)
    (i_z : toOneStepDevissage.i.left z = x)
    (π_z : toOneStepDevissage.π.left z = y)
    (distinguishedFiber : toOneStepDevissage.π.left ⁻¹' {y} = {z})
    (basePoint : toOneStepDevissage.Y.hom y = X.hom x)
    (residueExtension :
      let Y := toOneStepDevissage.Y
      ((S.residueFieldCongr basePoint).inv ≫
        Y.hom.residueFieldMap y).hom.IsPurelyTranscendental) :
    OneStepDevissageAtPoint X F x where
  toOneStepDevissage := toOneStepDevissage
  maximalSupportDimension := maximalSupportDimension
  z := z
  y := y
  i_z := i_z
  π_z := π_z
  distinguishedFiber := distinguishedFiber
  basePoint := basePoint
  residueExtension := residueExtension

/-- The support-point formulation supplies the ambient-point maximal-dimension condition. -/
theorem ofSupportPoint_maximalSupportDimension (D : OneStepDevissageAt X F x) :
    fiberSupportDimensionAt X.hom F x =
      fiberSupportDimension X.hom F (X.hom x) := sorry

/-- Regard a support-point one-step dévissage as one at the underlying ambient fibre point. -/
def ofSupportPoint (D : OneStepDevissageAt X F x) : OneStepDevissageAtPoint X F x where
  toOneStepDevissage := D.toOneStepDevissage
  maximalSupportDimension := ofSupportPoint_maximalSupportDimension D
  z := D.z
  y := D.y
  i_z := D.i_z
  π_z := D.π_z
  distinguishedFiber := D.distinguishedFiber
  basePoint := D.basePoint
  residueExtension := D.residueExtension

/-- The two maps from the distinguished auxiliary point have the prescribed values. -/
theorem mapsDistinguishedPoint (D : OneStepDevissageAtPoint X F x) :
    let E := D.toOneStepDevissage
    E.i.left D.z = x ∧ E.π.left D.z = D.y := sorry

end OneStepDevissageAtPoint

end AlgebraicGeometry.Scheme.Modules
