/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Ample.RelativeVery
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.TensorPower
public import ReasLib.AlgebraicGeometry.Scheme.OverField.Nodal
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.ProperDualizingComplex.Curve
public import ReasLib.AlgebraicGeometry.Scheme.Variety.Curve.ArithmeticGenus

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.Scheme.DerivedQCoh.ProperDualizingComplex
open scoped MonoidalCategory

universe u

namespace AlgebraicGeometry.SchemeOverField

/-- For a proper one-dimensional scheme over a field whose global functions are exactly
the ground field, with genus at least two, at-worst-nodal singularities, and ample dualizing
sheaf, the third tensor power of the dualizing sheaf is relatively very ample. -/
@[stacks 0E8X]
theorem tricanonicalVeryAmple
    {k : Type u} [Field k] (X : SchemeOverField k)
    [IsProper X.hom]
    (h_dimension_one : topologicalKrullDim X.left = 1)
    (h_global :
      Function.Bijective (Scheme.Hom.globalSectionsMap X.hom))
    (h_genus : (2 : ℕ) ≤ genus X h_dimension_one h_global)
    (h_at_worst_nodal : atWorstNodal X)
    (h_ample : Scheme.Modules.isAmpleObject (curveDualizingModule X.hom)) :
    RelativelyVeryAmple X.hom
      (RingedSpace.TensorPower.sheaf (curveDualizingModule X.hom) 3) := sorry

/-- For a proper one-dimensional scheme over a field whose global functions are exactly
the ground field, with genus at least two, at-worst-nodal singularities, and ample dualizing
sheaf, the first cohomology of the third tensor power of the dualizing sheaf vanishes. -/
@[stacks 0E8X]
theorem tricanonicalH1Vanishing
    {k : Type u} [Field k] (X : SchemeOverField k)
    [IsProper X.hom]
    (h_dimension_one : topologicalKrullDim X.left = 1)
    (h_global :
      Function.Bijective (Scheme.Hom.globalSectionsMap X.hom))
    (h_genus : (2 : ℕ) ≤ genus X h_dimension_one h_global)
    (h_at_worst_nodal : atWorstNodal X)
    (h_ample : Scheme.Modules.isAmpleObject (curveDualizingModule X.hom)) :
    IsZero (Scheme.Hom.cohomology X.hom
      (RingedSpace.TensorPower.sheaf (curveDualizingModule X.hom) 3) 1) := sorry

end AlgebraicGeometry.SchemeOverField
