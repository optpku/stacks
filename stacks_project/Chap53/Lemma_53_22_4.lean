module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Module.Curve.GlobalGeneration

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open AlgebraicGeometry.Scheme
open scoped MonoidalCategory

noncomputable section

universe u

namespace AlgebraicGeometry.SchemeOverField

/- Lemma 53.22.4 (1): for an integral proper curve with constant global functions,
an invertible module whose degree is at least `2 * genus X - 1 + deg Z` is globally generated,
where `Z` is a nonempty zero-dimensional closed subscheme. -/
@[stacks 0E3D] #check
  (AlgebraicGeometry.SchemeOverField.isGloballyGenerated_of_curveDegree_ge_genus_bound :
    ∀ {k : Type u} [Field k] (X : SchemeOverField k) [IsProper X.hom]
      [IsIntegral X.left]
      (h_dimension : topologicalKrullDim X.left = 1)
      (hΓ : Function.Bijective (Scheme.Hom.globalSectionsMap X.hom))
      (L : X.left.Modules) [Scheme.Modules.Invertible L]
      (Z : X.left.IdealSheafData) [Nonempty Z.subscheme]
      (hZ_dimension : topologicalKrullDim Z.subscheme = 0)
      (h_degree : 2 * (genus X h_dimension hΓ : ℤ) - 1 +
        (Module.finrank k (Scheme.Hom.globalSectionsAlg (Z.subschemeι ≫ X.hom)) : ℤ) ≤
        Scheme.Modules.curveDegreeOfInvertible X.hom h_dimension.le L),
      SheafOfModules.IsGloballyGenerated L)

/- Lemma 53.22.4 (2): under the same hypotheses, global sections of the invertible module
restrict surjectively along the inclusion of the nonempty zero-dimensional closed subscheme `Z`. -/
@[stacks 0E3D] #check
  (AlgebraicGeometry.SchemeOverField.sectionsPullback_surjective_of_curveDegree_ge_genus_bound :
    ∀ {k : Type u} [Field k] (X : SchemeOverField k) [IsProper X.hom]
      [IsIntegral X.left]
      (h_dimension : topologicalKrullDim X.left = 1)
      (hΓ : Function.Bijective (Scheme.Hom.globalSectionsMap X.hom))
      (L : X.left.Modules) [Scheme.Modules.Invertible L]
      (Z : X.left.IdealSheafData) [Nonempty Z.subscheme]
      (hZ_dimension : topologicalKrullDim Z.subscheme = 0)
      (h_degree : 2 * (genus X h_dimension hΓ : ℤ) - 1 +
        (Module.finrank k (Scheme.Hom.globalSectionsAlg (Z.subschemeι ≫ X.hom)) : ℤ) ≤
        Scheme.Modules.curveDegreeOfInvertible X.hom h_dimension.le L),
      Function.Surjective (Scheme.Modules.sectionsPullback Z.subschemeι L))

end AlgebraicGeometry.SchemeOverField
