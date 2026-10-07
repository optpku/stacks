module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.ProjectiveSpace.ClosedSubscheme.Genus

open CategoryTheory Set TopologicalSpace

universe u

namespace AlgebraicGeometry.ProjectiveSpace.ClosedSubscheme

/- Lemma 53.9.3 (1): the canonical map from the ground field to the global
sections of a nonempty equidimensional plane curve with no embedded points is bijective. -/
@[stacks 0BYD] #check
  (AlgebraicGeometry.ProjectiveSpace.ClosedSubscheme.planeCurve_globalSectionsMap_bijective :
    ∀ (k : Type u) [Field k]
    (Z : (ProjectiveSpace.scheme k 2).IdealSheafData)
    [Nonempty Z.subscheme]
    (P : ProjTwistPresentation (ProjectiveSpace.grading k 2))
    [h_componentDim : Fact (∀ C : irreducibleComponents Z.subscheme,
      topologicalKrullDim (C : Set Z.subscheme) = 1)]
    [h_noEmbeddedPoints : Fact (Z.subscheme.embeddedPoints = (∅ : Set Z.subscheme))]
    (F : MvPolynomial (Fin 3) k)
    (h_generator : (twistIdeal 2 Z P).toIdeal = Ideal.span {F}),
    Function.Bijective
      (Scheme.Hom.globalSectionsMap (Z.subschemeι ≫ ProjectiveSpace.toSpec k 2)))

/- Lemma 53.9.3 (2): the first structure-sheaf cohomology of a nonempty
equidimensional plane curve has dimension `(deg(F) - 1) * (deg(F) - 2) / 2`. -/
@[stacks 0BYD] #check
  (AlgebraicGeometry.ProjectiveSpace.ClosedSubscheme.planeCurve_genus_eq_totalDegree :
    ∀ (k : Type u) [Field k]
    (Z : (ProjectiveSpace.scheme k 2).IdealSheafData)
    [Nonempty Z.subscheme]
    (P : ProjTwistPresentation (ProjectiveSpace.grading k 2))
    [h_componentDim : Fact (∀ C : irreducibleComponents Z.subscheme,
      topologicalKrullDim (C : Set Z.subscheme) = 1)]
    [h_noEmbeddedPoints : Fact (Z.subscheme.embeddedPoints = (∅ : Set Z.subscheme))]
    (F : MvPolynomial (Fin 3) k)
    (h_generator : (twistIdeal 2 Z P).toIdeal = Ideal.span {F}),
    Scheme.Hom.cohomologyFinrank
      (Z.subschemeι ≫ ProjectiveSpace.toSpec k 2)
      (SheafOfModules.unit Z.subscheme.ringCatSheaf : Z.subscheme.Modules) 1 =
      ((F.totalDegree - 1) * (F.totalDegree - 2)) / 2)

end AlgebraicGeometry.ProjectiveSpace.ClosedSubscheme
