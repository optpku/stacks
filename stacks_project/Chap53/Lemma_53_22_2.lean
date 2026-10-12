/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Module.Curve.Cohomology.IdealTensor

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open AlgebraicGeometry.Scheme
open scoped MonoidalCategory

noncomputable section

universe u

namespace AlgebraicGeometry.SchemeOverField

/- Lemma 53.22.2 (1): under the Situation 53.6.2 hypotheses, if the degree of an
invertible module exceeds `2 * genus X - 2 + deg Z`, then the first cohomology of
`Z.toModule ⊗ L` vanishes. -/
@[stacks 0E3B] #check
  (AlgebraicGeometry.SchemeOverField.firstCohomology_isZero_of_idealTensor_degree_gt :
    ∀ {k : Type u} [Field k] (X : SchemeOverField k) [IsProper X.hom]
    [IsIntegral X.left]
    (h_dimension : topologicalKrullDim X.left = 1)
    (hΓ : Function.Bijective (Scheme.Hom.globalSectionsMap X.hom))
    (L : X.left.Modules) [Scheme.Modules.Invertible L]
    (Z : X.left.IdealSheafData)
    (hZ_dimension : topologicalKrullDim Z.subscheme ≤ 0)
    (h_degree : Scheme.Modules.curveDegreeOfInvertible X.hom h_dimension.le L >
      2 * (genus X h_dimension hΓ : ℤ) - 2 +
        (Module.finrank k
          (Scheme.Hom.globalSectionsAlg (Z.subschemeι ≫ X.hom)) : ℤ)),
    IsZero (Scheme.Hom.cohomology X.hom (Z.toModule ⊗ L) 1))

/- Lemma 53.22.2 (2): under the same hypotheses and strict degree bound, either
`H⁰(X, Z.toModule ⊗ L)` is nonzero, or `genus X = 0` and the degree of `L` is
`deg Z - 1`. -/
@[stacks 0E3B] #check
  (AlgebraicGeometry.SchemeOverField.globalSections_nonzero_or_genus_zero_of_idealTensor_degree_gt :
    ∀ {k : Type u} [Field k] (X : SchemeOverField k) [IsProper X.hom]
    [IsIntegral X.left]
    (h_dimension : topologicalKrullDim X.left = 1)
    (hΓ : Function.Bijective (Scheme.Hom.globalSectionsMap X.hom))
    (L : X.left.Modules) [Scheme.Modules.Invertible L]
    (Z : X.left.IdealSheafData)
    (hZ_dimension : topologicalKrullDim Z.subscheme ≤ 0)
    (h_degree : Scheme.Modules.curveDegreeOfInvertible X.hom h_dimension.le L >
      2 * (genus X h_dimension hΓ : ℤ) - 2 +
        (Module.finrank k
          (Scheme.Hom.globalSectionsAlg (Z.subschemeι ≫ X.hom)) : ℤ)),
    (¬ IsZero (Scheme.Hom.cohomology X.hom (Z.toModule ⊗ L) 0)) ∨
      (genus X h_dimension hΓ = 0 ∧
        Scheme.Modules.curveDegreeOfInvertible X.hom h_dimension.le L =
          (Module.finrank k
            (Scheme.Hom.globalSectionsAlg (Z.subschemeι ≫ X.hom)) : ℤ) - 1))

/- Lemma 53.22.2 (3): in the exceptional case with empty `Z`, the curve is
isomorphic over `k` to the projective line and `L` is isomorphic to the pullback
of the degree `-1` twisting sheaf. -/
@[stacks 0E3B] #check
  (AlgebraicGeometry.SchemeOverField.projectiveLine_of_empty_ideal_exceptional_case :
    ∀ {k : Type u} [Field k] (X : SchemeOverField k) [IsProper X.hom]
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
    (hZ_empty : Z = (⊤ : X.left.IdealSheafData)),
    ∃ e : X ≅ Over.mk (ProjectiveLine.toSpec k),
      IsIsomorphic L
        ((Scheme.Modules.pullback e.hom.left).obj
          (ProjectiveSpace.twistingSheaf k 1 (-1))))

end AlgebraicGeometry.SchemeOverField
