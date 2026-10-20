/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.IdealSubobject
public import ReasLib.AlgebraicGeometry.Scheme.Module.Curve.Degree
public import ReasLib.AlgebraicGeometry.Scheme.Variety.Curve.ArithmeticGenus
public import ReasLib.AlgebraicGeometry.ProjectiveSpace.Line
public import ReasLib.AlgebraicGeometry.ProjectiveSpace.Twist

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open AlgebraicGeometry.Scheme
open scoped MonoidalCategory

noncomputable section

universe u

namespace AlgebraicGeometry.SchemeOverField

/-- On an integral proper curve over `k` whose global functions are `k`, the first
cohomology of `Z.toModule ⊗ L` vanishes if `L` is invertible, the closed subscheme
`Z` has dimension at most zero, and `deg L > 2 * genus X - 2 + deg Z`, where
`deg Z` is the `k`-dimension of its global sections. -/
@[stacks 0E3B]
theorem firstCohomology_isZero_of_idealTensor_degree_gt
    {k : Type u} [Field k] (X : SchemeOverField k) [IsProper X.hom]
    [IsIntegral X.left]
    (h_dimension : topologicalKrullDim X.left = 1)
    (hΓ : Function.Bijective (Scheme.Hom.globalSectionsMap X.hom))
    (L : X.left.Modules) [Scheme.Modules.Invertible L]
    (Z : X.left.IdealSheafData)
    (hZ_dimension : topologicalKrullDim Z.subscheme ≤ 0)
    (h_degree : Scheme.Modules.curveDegreeOfInvertible X.hom h_dimension.le L >
      2 * (genus X h_dimension hΓ : ℤ) - 2 +
        (Module.finrank k
          (Scheme.Hom.globalSectionsAlg (Z.subschemeι ≫ X.hom)) : ℤ)) :
    IsZero (Scheme.Hom.cohomology X.hom (Z.toModule ⊗ L) 1) := sorry

/-- On an integral proper curve over `k` whose global functions are `k`, if `L` is
invertible, `Z` has dimension at most zero, and `deg L > 2 * genus X - 2 + deg Z`,
then `Z.toModule ⊗ L` has nonzero global sections or the genus is zero and
`deg L = deg Z - 1`, where `deg Z` is the `k`-dimension of its global sections. -/
@[stacks 0E3B]
theorem globalSections_nonzero_or_genus_zero_of_idealTensor_degree_gt
    {k : Type u} [Field k] (X : SchemeOverField k) [IsProper X.hom]
    [IsIntegral X.left]
    (h_dimension : topologicalKrullDim X.left = 1)
    (hΓ : Function.Bijective (Scheme.Hom.globalSectionsMap X.hom))
    (L : X.left.Modules) [Scheme.Modules.Invertible L]
    (Z : X.left.IdealSheafData)
    (hZ_dimension : topologicalKrullDim Z.subscheme ≤ 0)
    (h_degree : Scheme.Modules.curveDegreeOfInvertible X.hom h_dimension.le L >
      2 * (genus X h_dimension hΓ : ℤ) - 2 +
        (Module.finrank k
          (Scheme.Hom.globalSectionsAlg (Z.subschemeι ≫ X.hom)) : ℤ)) :
    (¬ IsZero (Scheme.Hom.cohomology X.hom (Z.toModule ⊗ L) 0)) ∨
      (genus X h_dimension hΓ = 0 ∧
        Scheme.Modules.curveDegreeOfInvertible X.hom h_dimension.le L =
          (Module.finrank k
            (Scheme.Hom.globalSectionsAlg (Z.subschemeι ≫ X.hom)) : ℤ) - 1) := sorry

/-- An integral proper curve over `k` with global functions `k`, genus zero, and
an invertible module of degree `deg Z - 1` satisfying
`deg L > 2 * genus X - 2 + deg Z` for an empty closed subscheme `Z` is isomorphic
over `k` to the projective line, identifying `L` with the pullback of its
degree `-1` twisting sheaf. -/
@[stacks 0E3B]
theorem projectiveLine_of_empty_ideal_exceptional_case
    {k : Type u} [Field k] (X : SchemeOverField k) [IsProper X.hom]
    [IsIntegral X.left]
    (h_dimension : topologicalKrullDim X.left = 1)
    (hΓ : Function.Bijective (Scheme.Hom.globalSectionsMap X.hom))
    (L : X.left.Modules) [Scheme.Modules.Invertible L]
    (Z : X.left.IdealSheafData)
    (hZ_dimension : topologicalKrullDim Z.subscheme ≤ 0)
    (h_degree : Scheme.Modules.curveDegreeOfInvertible X.hom h_dimension.le L >
      2 * (genus X h_dimension hΓ : ℤ) - 2 +
        (Module.finrank k
          (Scheme.Hom.globalSectionsAlg (Z.subschemeι ≫ X.hom)) : ℤ))
    (h_case_two : genus X h_dimension hΓ = 0 ∧
      Scheme.Modules.curveDegreeOfInvertible X.hom h_dimension.le L =
        (Module.finrank k
          (Scheme.Hom.globalSectionsAlg (Z.subschemeι ≫ X.hom)) : ℤ) - 1)
    (hZ_empty : Z = (⊤ : X.left.IdealSheafData)) :
    ∃ e : X ≅ Over.mk (ProjectiveLine.toSpec k),
      IsIsomorphic L
        ((Scheme.Modules.pullback e.hom.left).obj
          (ProjectiveSpace.twistingSheaf k 1 (-1))) := sorry

end AlgebraicGeometry.SchemeOverField
