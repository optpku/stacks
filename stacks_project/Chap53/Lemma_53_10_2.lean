module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Module.Curve.Cohomology.GenusZero
public import ReasLib.AlgebraicGeometry.Scheme.Module.Curve.VeryAmple.GenusZero

universe u

open CategoryTheory
open AlgebraicGeometry
open ProjectiveSpace.VectorSpace.LinearSystem
open scoped AlgebraicGeometry

/- Lemma 53.10.2 (1): a positive-degree invertible module on a proper genus-zero curve has
global sections of dimension one more than its degree. -/
@[stacks 0C6T] #check
  (AlgebraicGeometry.SchemeOverField.cohomologyFinrank_zero_eq_degree_add_one_of_genus_zero :
    ∀ {k : Type u} [Field k] (X : AlgebraicGeometry.SchemeOverField k)
      [AlgebraicGeometry.Curve X] [AlgebraicGeometry.IsProper X.hom]
      (hΓ : Function.Bijective (AlgebraicGeometry.Scheme.Hom.globalSectionsMap X.hom))
      (h_genus : AlgebraicGeometry.Scheme.Hom.cohomologyFinrank X.hom
        (SheafOfModules.unit X.left.ringCatSheaf : X.left.Modules) 1 = 0)
      (L : X.left.Modules) [AlgebraicGeometry.Scheme.Modules.Invertible L] (d : ℕ)
      (h_degree : AlgebraicGeometry.Scheme.Modules.curveDegreeOfInvertible X.hom
        (AlgebraicGeometry.topologicalKrullDim_eq_one X).le L = (d : ℤ))
      (h_positive : 0 < d),
      AlgebraicGeometry.Scheme.Hom.cohomologyFinrank X.hom L 0 = d + 1)

/- Lemma 53.10.2 (2): a positive-degree invertible module on a proper genus-zero curve has
vanishing first cohomology. -/
@[stacks 0C6T] #check
  (AlgebraicGeometry.SchemeOverField.cohomologyFinrank_one_eq_zero_of_genus_zero :
    ∀ {k : Type u} [Field k] (X : AlgebraicGeometry.SchemeOverField k)
      [AlgebraicGeometry.Curve X] [AlgebraicGeometry.IsProper X.hom]
      (hΓ : Function.Bijective (AlgebraicGeometry.Scheme.Hom.globalSectionsMap X.hom))
      (h_genus : AlgebraicGeometry.Scheme.Hom.cohomologyFinrank X.hom
        (SheafOfModules.unit X.left.ringCatSheaf : X.left.Modules) 1 = 0)
      (L : X.left.Modules) [AlgebraicGeometry.Scheme.Modules.Invertible L] (d : ℕ)
      (h_degree : AlgebraicGeometry.Scheme.Modules.curveDegreeOfInvertible X.hom
        (AlgebraicGeometry.topologicalKrullDim_eq_one X).le L = (d : ℤ))
      (h_positive : 0 < d),
      AlgebraicGeometry.Scheme.Hom.cohomologyFinrank X.hom L 1 = 0)

/- Lemma 53.10.2 (3): a positive-degree invertible module on a proper genus-zero curve is
relatively very ample. -/
@[stacks 0C6T] #check
  (AlgebraicGeometry.SchemeOverField.relativelyVeryAmple_of_genus_zero_of_positive_degree :
    ∀ {k : Type u} [Field k] (X : AlgebraicGeometry.SchemeOverField k)
      [AlgebraicGeometry.Curve X] [AlgebraicGeometry.IsProper X.hom]
      (hΓ : Function.Bijective (AlgebraicGeometry.Scheme.Hom.globalSectionsMap X.hom))
      (h_genus : AlgebraicGeometry.Scheme.Hom.cohomologyFinrank X.hom
        (SheafOfModules.unit X.left.ringCatSheaf : X.left.Modules) 1 = 0)
      (L : X.left.Modules) [AlgebraicGeometry.Scheme.Modules.Invertible L] (d : ℕ)
      (h_degree : AlgebraicGeometry.Scheme.Modules.curveDegreeOfInvertible X.hom
        (AlgebraicGeometry.topologicalKrullDim_eq_one X).le L = (d : ℤ))
      (h_positive : 0 < d),
      AlgebraicGeometry.RelativelyVeryAmple X.hom L)

/- Lemma 53.10.2 (4): a basis of all global sections defines a closed immersion into projective
space of dimension `d`. -/
@[stacks 0C6T] #check
  (AlgebraicGeometry.SchemeOverField.exists_basis_closedImmersion_projectiveSpace_of_genus_zero :
    ∀ {k : Type u} [Field k] (X : AlgebraicGeometry.SchemeOverField k)
      [AlgebraicGeometry.Curve X] [AlgebraicGeometry.IsProper X.hom]
      (hΓ : Function.Bijective (AlgebraicGeometry.Scheme.Hom.globalSectionsMap X.hom))
      (h_genus : AlgebraicGeometry.Scheme.Hom.cohomologyFinrank X.hom
        (SheafOfModules.unit X.left.ringCatSheaf : X.left.Modules) 1 = 0)
      (L : X.left.Modules) [AlgebraicGeometry.Scheme.Modules.Invertible L] (d : ℕ)
      (h_degree : AlgebraicGeometry.Scheme.Modules.curveDegreeOfInvertible X.hom
        (AlgebraicGeometry.topologicalKrullDim_eq_one X).le L = (d : ℤ))
      (h_positive : 0 < d),
      ∃ (b : Module.Basis (Fin (d + 1)) k
          (AlgebraicGeometry.SchemeOverField.globalSectionsMod X L))
        (i : X.left ⟶ AlgebraicGeometry.ProjectiveSpace.scheme k d),
        AlgebraicGeometry.ProjectiveSpace.VectorSpace.LinearSystem.BasisMorphismSpec d b X L
            (𝟙 (AlgebraicGeometry.SchemeOverField.globalSectionsMod X L)) i ∧
          AlgebraicGeometry.IsClosedImmersion i ∧
            i ≫ AlgebraicGeometry.ProjectiveSpace.toSpec k d = X.hom)
