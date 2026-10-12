/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.ProjectiveSpace.Hypersurface
public import ReasLib.AlgebraicGeometry.Scheme.Gorenstein
public import ReasLib.AlgebraicGeometry.Scheme.Variety.Curve
public import ReasLib.AlgebraicGeometry.Scheme.Variety.Curve.ArithmeticGenus

@[expose] public section

open CategoryTheory
open AlgebraicGeometry
open AlgebraicGeometry.ProjectiveSpace.ClosedSubscheme
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.SchemeOverField

/-- A proper Gorenstein genus-zero curve with only constant global functions is isomorphic over
the ground field to a plane curve of degree two. -/
theorem exists_planeCurve_degree_two_of_genus_zero
    {k : Type u} [Field k] (X : SchemeOverField k) [Curve X] [IsProper X.hom]
    [Scheme.Gorenstein X.left]
    (hΓ : Function.Bijective (Scheme.Hom.globalSectionsMap X.hom))
    (h_genus : SchemeOverField.genus X (topologicalKrullDim_eq_one X) hΓ = 0) :
    ∃ (Z : (ProjectiveSpace.scheme k 2).IdealSheafData)
      (F : MvPolynomial (Fin 3) k),
      Nonempty (X ≅ Over.mk (Z.subschemeι ≫ ProjectiveSpace.toSpec k 2)) ∧
        HasHomogeneousEquation 2 Z F ∧ F.totalDegree = 2 := sorry

end AlgebraicGeometry.SchemeOverField
