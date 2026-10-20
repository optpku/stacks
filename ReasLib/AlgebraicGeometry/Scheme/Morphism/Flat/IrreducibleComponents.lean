/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
public import ReasLib.AlgebraicGeometry.Scheme.ClosedSubscheme.PointClosure.Integral
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.DimensionFormula.Flat

/-!
# Irreducible components under flat morphisms

This file records the generic-point and dimension behavior of irreducible components under
flat morphisms.
-/

@[expose] public section

open CategoryTheory TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Hom

/-- The reduced closure of a generic point of the source of a flat morphism to an integral
scheme maps its generic point to the generic point of the target. -/
theorem flatComponent_mapsGenericPoint
    {X Y : Scheme.{u}} [IsIntegral Y] (f : X ⟶ Y) [Flat f]
    (η : genericPoints X) :
    (Scheme.PointClosure.ι η.1 ≫ f)
        (genericPoint (Scheme.PointClosure.scheme η.1)) =
      genericPoint Y := sorry

/-- Every irreducible component of the source has the relative `δ`-dimension prescribed by
the dimension of the integral target and the relative dimension of a flat morphism. -/
theorem flatComponent_dimension
    {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    (X Y : Over S) [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    [IsIntegral Y.left] (k : ℤ)
    (hY : Y.hom.relativeDimensionFunction δ (genericPoint Y.left) = k)
    (f : X ⟶ Y) (r : ℕ) [Flat f.left] [Scheme.Hom.RelativeDimension f.left r]
    (η : genericPoints X.left) :
    X.hom.relativeDimensionFunction δ η.1 =
      ((k - 1) + (r : ℤ)) + 1 := sorry

end AlgebraicGeometry.Scheme.Hom
