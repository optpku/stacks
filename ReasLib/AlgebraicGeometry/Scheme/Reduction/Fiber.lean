/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Fiber
public import ReasLib.AlgebraicGeometry.Scheme.Reduction.Functor

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Hom

/-- The compatibility equation defining the reduction--fibre comparison. -/
theorem reductionFiberComparison_condition {X Y : Scheme.{u}} (f : X ⟶ Y) (y : Y) :
    reductionMap (f.fiberι y) ≫ reductionι X ≫ f =
      reductionι (f.fiber y) ≫ f.fiberToSpecResidueField y ≫ Y.fromSpecResidueField y := sorry

/-- The canonical morphism from the reduction of a fibre to the fibre of the reduced morphism. -/
noncomputable def reductionFiberComparison {X Y : Scheme.{u}} (f : X ⟶ Y) (y : Y) :
    reduction (f.fiber y) ⟶ (reductionι X ≫ f).fiber y :=
  pullback.lift (reductionMap (f.fiberι y))
    (reductionι (f.fiber y) ≫ f.fiberToSpecResidueField y)
    (reductionFiberComparison_condition f y)

/-- The comparison morphism is compatible with the fibre projection to the reduced source. -/
theorem reductionFiberComparison_fiberι {X Y : Scheme.{u}} (f : X ⟶ Y) (y : Y) :
    reductionFiberComparison f y ≫ (reductionι X ≫ f).fiberι y =
      reductionMap (f.fiberι y) := sorry

/-- The comparison morphism is compatible with the projection to the residue-field scheme. -/
theorem reductionFiberComparison_fiberToSpecResidueField
    {X Y : Scheme.{u}} (f : X ⟶ Y) (y : Y) :
    reductionFiberComparison f y ≫ (reductionι X ≫ f).fiberToSpecResidueField y =
      reductionι (f.fiber y) ≫ f.fiberToSpecResidueField y := sorry

/-- At a generic point, reduction of a fibre is canonically isomorphic to the fibre of the
reduced morphism. -/
@[instance]
theorem reductionFiberComparison_isIso {X Y : Scheme.{u}} (f : X ⟶ Y)
    (η : genericPoints Y) : IsIso (reductionFiberComparison f η) := sorry

end AlgebraicGeometry.Scheme.Hom
