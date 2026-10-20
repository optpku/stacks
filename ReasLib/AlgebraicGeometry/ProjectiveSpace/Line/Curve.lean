/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.ProjectiveSpace.Over
public import ReasLib.AlgebraicGeometry.ProjectiveSpace.Proper
public import ReasLib.AlgebraicGeometry.Scheme.Variety.Curve
public import ReasLib.AlgebraicGeometry.Scheme.Regular
public import ReasLib.AlgebraicGeometry.Scheme.Variety.Curve.ArithmeticGenus

@[expose] public section

open CategoryTheory
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.ProjectiveSpace

/-- The standard projective line over a field is a curve. -/
instance instCurveLine (k : Type u) [Field k] : Curve (schemeOver k 1) := sorry

/-- The standard projective line over a field is regular. -/
instance instRegularLine (k : Type u) [Field k] : Scheme.Regular (scheme k 1) := sorry

/-- The structure morphism of the projective line induces a bijection on global sections. -/
theorem line_globalSectionsMap_bijective (k : Type u) [Field k] :
    Function.Bijective (Scheme.Hom.globalSectionsMap (toSpec k 1)) := sorry

/-- The standard projective line over a field has genus zero. -/
theorem line_genus_eq_zero (k : Type u) [Field k] :
    @SchemeOverField.genus k _ (schemeOver k 1) (toSpec_isProper k 1)
      (topologicalKrullDim_eq_one (schemeOver k 1)) (line_globalSectionsMap_bijective k) = 0 := sorry

end AlgebraicGeometry.ProjectiveSpace
