module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.ApproximationByPerfectComplexes.Affine

@[expose] public section

noncomputable section

universe u

/- Lemma 36.14.4 (1): on an affine scheme, an `m`-pseudo-coherent quasicoherent
derived object whose cohomology is supported on `T` from degree `m - r + 1` onward has
a perfect approximation through degree `m` when the complement of `T` has an affine open
cover indexed by `Fin r`. -/
@[stacks 08EQ] #check
  (AlgebraicGeometry.Scheme.HasPerfectApproximation.of_isAffine :
    ∀ {X : AlgebraicGeometry.Scheme.{u}} [AlgebraicGeometry.IsAffine X]
      (T : TopologicalSpace.Closeds X)
      (E : CategoryTheory.DerivedCategory.CohomologyIn
        (AlgebraicGeometry.RingedSpace.quasiCoherentModuleProperty X.toRingedSpace))
      (m : ℤ) (r : ℕ),
      AlgebraicGeometry.Scheme.AffineOpenCover.HasCard
          (T.compl : AlgebraicGeometry.Scheme) r →
        AlgebraicGeometry.RingedSpace.ModuleDerived.IsMPseudoCoherent E.obj m →
          (∀ i : ℤ, m - (r : ℤ) + 1 ≤ i →
            AlgebraicGeometry.RingedSpace.moduleSupportedOn (T : Set X)
              (AlgebraicGeometry.RingedSpace.ModuleDerived.cohomologySheaf E.obj i)) →
            AlgebraicGeometry.Scheme.HasPerfectApproximation T E m)

/- Lemma 36.14.4 (2): every affine scheme admits approximation by perfect complexes. -/
@[stacks 08EQ] #check
  (AlgebraicGeometry.Scheme.HasApproximationByPerfectComplexes.of_isAffine :
    ∀ (X : AlgebraicGeometry.Scheme.{u}) [AlgebraicGeometry.IsAffine X],
      AlgebraicGeometry.Scheme.HasApproximationByPerfectComplexes X)
