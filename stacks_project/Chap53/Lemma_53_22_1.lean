/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Curve.Cohomology.DegreeBound
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open AlgebraicGeometry.Scheme
open Scheme.DerivedQCoh.ProperDualizingComplex
open scoped MonoidalCategory

noncomputable section

universe u

namespace AlgebraicGeometry.SchemeOverField

/- Lemma 53.22.1 (1): let `X` be an integral proper curve over `k` whose global
functions are `k`, let `L` be an invertible module on `X`, and let `Z` be a
closed subscheme of dimension at most zero, possibly empty, with ideal module
`Z.toModule`. If
`H¹(X, Z.toModule ⊗ L)` is nonzero, then
`deg L ≤ 2 * genus X h_dimension hΓ - 2 + deg Z`, where `deg Z` is the
`k`-dimension of its global sections. -/
@[stacks 0E3A] #check
  (AlgebraicGeometry.SchemeOverField.curveDegree_le_of_idealTensor_cohomology_one_nonzero :
    ∀ {k : Type u} [Field k] (X : SchemeOverField k) [IsProper X.hom]
    [IsIntegral X.left]
    (h_dimension : topologicalKrullDim X.left = 1)
    (hΓ : Function.Bijective (Scheme.Hom.globalSectionsMap X.hom))
    (L : X.left.Modules) [Scheme.Modules.Invertible L]
    (Z : X.left.IdealSheafData)
    (hZ_dimension : topologicalKrullDim Z.subscheme ≤ 0)
    (hH1 : ¬ IsZero (Scheme.Hom.cohomology X.hom (Z.toModule ⊗ L) 1)),
    Scheme.Modules.curveDegreeOfInvertible X.hom h_dimension.le L ≤
      2 * (genus X h_dimension hΓ : ℤ) - 2 +
        (Module.finrank k
          (Scheme.Hom.globalSectionsAlg (Z.subschemeι ≫ X.hom)) : ℤ))

/- Lemma 53.22.1 (2): under the hypotheses of Lemma 53.22.1 (1), allowing the
closed subscheme `Z` to be empty, the degree bound is strict when the
ideal-tensor module `Z.toModule ⊗ L` is not
isomorphic to the curve dualizing module `curveDualizingModule X.hom`. -/
@[stacks 0E3A] #check
  (AlgebraicGeometry.SchemeOverField.curveDegree_lt_of_idealTensor_cohomology_one_nonzero_of_not_iso :
    ∀ {k : Type u} [Field k] (X : SchemeOverField k) [IsProper X.hom]
    [IsIntegral X.left]
    (h_dimension : topologicalKrullDim X.left = 1)
    (hΓ : Function.Bijective (Scheme.Hom.globalSectionsMap X.hom))
    (L : X.left.Modules) [Scheme.Modules.Invertible L]
    (Z : X.left.IdealSheafData)
    (hZ_dimension : topologicalKrullDim Z.subscheme ≤ 0)
    (hH1 : ¬ IsZero (Scheme.Hom.cohomology X.hom (Z.toModule ⊗ L) 1))
    (h_not_iso : ¬ Nonempty
      ((Z.toModule ⊗ L) ≅ curveDualizingModule X.hom)),
    Scheme.Modules.curveDegreeOfInvertible X.hom h_dimension.le L <
      2 * (genus X h_dimension hΓ : ℤ) - 2 +
        (Module.finrank k
          (Scheme.Hom.globalSectionsAlg (Z.subschemeι ≫ X.hom)) : ℤ))

end AlgebraicGeometry.SchemeOverField
