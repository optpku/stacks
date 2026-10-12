/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.SiteComparison

universe u

/- Lemma 36.41.1 (1): `D_QCoh(𝒪_X)` and the quasi-coherent derived category of
the small Zariski ringed site are canonically exact equivalent. -/
@[stacks 0GZZ]
#check
  (AlgebraicGeometry.Scheme.DerivedQCoh.smallZariskiEquivalence :
    ∀ (X : AlgebraicGeometry.Scheme.{u}),
      CategoryTheory.RLinear.TriangulatedEquivalence ℤ
        (CategoryTheory.DerivedCategory.CohomologyIn
          (AlgebraicGeometry.RingedSpace.quasiCoherentModuleProperty X.toRingedSpace))
        (AlgebraicGeometry.Scheme.DerivedQCoh.SmallZariski X))

/- Lemma 36.41.1 (2): the quasi-coherent derived categories of the small Zariski
site and its affine Zariski subsite are canonically exact equivalent. -/
@[stacks 0GZZ]
#check
  (AlgebraicGeometry.Scheme.DerivedQCoh.affineZariskiEquivalence :
    ∀ (X : AlgebraicGeometry.Scheme.{u}),
      CategoryTheory.RLinear.TriangulatedEquivalence ℤ
        (AlgebraicGeometry.Scheme.DerivedQCoh.SmallZariski X)
        (AlgebraicGeometry.Scheme.DerivedQCoh.AffineZariski X))

/- Lemma 36.41.1 (3): the quasi-coherent derived categories of the affine Zariski
and affine chaotic sites are canonically exact equivalent. -/
@[stacks 0GZZ]
#check
  (AlgebraicGeometry.Scheme.DerivedQCoh.affineTopologyEquivalence :
    ∀ (X : AlgebraicGeometry.Scheme.{u}),
      CategoryTheory.RLinear.TriangulatedEquivalence ℤ
        (AlgebraicGeometry.Scheme.DerivedQCoh.AffineZariski X)
        (AlgebraicGeometry.Scheme.DerivedQCoh.Affine X))

/- Lemma 36.41.1 (4): quasi-coherent cohomology on the affine chaotic site and
the comparison-map category `QC(X_affine, 𝒪)` are canonically exact equivalent. -/
@[stacks 0GZZ]
#check
  (AlgebraicGeometry.Scheme.DerivedQCoh.affineQCEquivalence :
    ∀ (X : AlgebraicGeometry.Scheme.{u}),
      CategoryTheory.RLinear.TriangulatedEquivalence ℤ
        (AlgebraicGeometry.Scheme.DerivedQCoh.Affine X)
        (AlgebraicGeometry.Scheme.DerivedQCoh.AffineQC X))
