module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.SiteModels
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.SiteComparison

universe u

/- Lemma 75.30.1 (1): `D_QCoh(𝒪_X)` and the quasi-coherent derived category of
the affine étale ringed site are canonically exact equivalent. -/
@[stacks 0H06]
#check
  (AlgebraicGeometry.AlgebraicSpace.DerivedQCoh.affineEtaleEquivalence :
    ∀ {S : AlgebraicGeometry.Scheme.{u}} (X : AlgebraicGeometry.AlgebraicSpace S),
      CategoryTheory.RLinear.TriangulatedEquivalence ℤ
        (AlgebraicGeometry.AlgebraicSpace.DerivedQCoh X)
        (AlgebraicGeometry.AlgebraicSpace.DerivedQCoh.AffineEtale X))

/- Lemma 75.30.1 (2): the quasi-coherent derived categories of the affine étale
site and the affine chaotic site are canonically exact equivalent. -/
@[stacks 0H06]
#check
  (AlgebraicGeometry.AlgebraicSpace.DerivedQCoh.affineTopologyEquivalence :
    ∀ {S : AlgebraicGeometry.Scheme.{u}} (X : AlgebraicGeometry.AlgebraicSpace S),
      CategoryTheory.RLinear.TriangulatedEquivalence ℤ
        (AlgebraicGeometry.AlgebraicSpace.DerivedQCoh.AffineEtale X)
        (AlgebraicGeometry.AlgebraicSpace.DerivedQCoh.Affine X))

/- Lemma 75.30.1 (3): quasi-coherent cohomology on the affine chaotic site and
the comparison-map category `QC(X_affine, 𝒪)` are canonically exact equivalent. -/
@[stacks 0H06]
#check
  (AlgebraicGeometry.AlgebraicSpace.DerivedQCoh.affineQCEquivalence :
    ∀ {S : AlgebraicGeometry.Scheme.{u}} (X : AlgebraicGeometry.AlgebraicSpace S),
      CategoryTheory.RLinear.TriangulatedEquivalence ℤ
        (AlgebraicGeometry.AlgebraicSpace.DerivedQCoh.Affine X)
        (AlgebraicGeometry.AlgebraicSpace.DerivedQCoh.AffineQC X))
