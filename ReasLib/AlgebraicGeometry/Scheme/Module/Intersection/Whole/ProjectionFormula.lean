module

public import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
public import ReasLib.AlgebraicGeometry.Scheme.Module.Ample
public import ReasLib.AlgebraicGeometry.Scheme.Module.Intersection.ProjectionFormula
public import ReasLib.AlgebraicGeometry.Scheme.Module.Intersection.Whole
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Integral.Dimension
public import ReasLib.AlgebraicGeometry.Scheme.Variety.Properties

/-!
# Projection formula for whole-scheme intersection degree

This file specializes the numerical-intersection projection formula to finite dominant
morphisms of proper varieties.
-/

@[expose] public section

open AlgebraicGeometry
open CategoryTheory
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules.Intersection

/-- Pullback along a finite dominant morphism of proper varieties multiplies whole-scheme
intersection degree by the induced function-field degree. -/
theorem wholeDegree_pullback_eq_inducedFunctionFieldDegree_mul
    {k : Type u} [Field k]
    {X Y : SchemeOverField k} [ProperVariety X] [ProperVariety Y]
    (f : Y ⟶ X) [IsFinite f.left] [IsDominant f.left]
    {dX dY : ℕ}
    (hXdim : topologicalKrullDim X.left = dX)
    (hYdim : topologicalKrullDim Y.left = dY)
    (L : X.left.Modules) [Invertible L] [IsAmple L] :
    wholeDegree k Y.hom ((Scheme.Modules.pullback f.left).obj L) hYdim =
      (f.left.inducedFunctionFieldDegree : ℚ) * wholeDegree k X.hom L hXdim := sorry

end AlgebraicGeometry.Scheme.Modules.Intersection
