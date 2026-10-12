/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap75.Lemma_75_14_5_Affine
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace CategoryTheory TopologicalSpace

universe u

/- Lemma 75.14.5 (1): on an algebraic space representable by an affine scheme, an
`m`-pseudo-coherent object of `DerivedQCoh` whose cohomology is supported on `T`
from degree `m - r + 1` onward has a perfect approximation through degree `m` when
`X \ T` is a union of `r` affine opens. -/
@[stacks 08HM] #check
  (HasPerfectApproximation.of_isAffine :
    ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} [IsAffine X]
      (T : Closeds (Points X)) (E : DerivedQCoh X) (m : ℤ) (r : ℕ),
      AffineOpenCover.HasCard (OpenSubspace.ofOpensSpace T.compl) r →
        IsMPseudoCoherent X E.obj m →
          (∀ i : ℤ, m - (r : ℤ) + 1 ≤ i →
            Modules.moduleSupportedOn (T : Set (Points X))
              ((DerivedCategory.homologyFunctor (Modules X) i).obj E.obj)) →
            HasPerfectApproximation T E m)

/- Lemma 75.14.5 (2): approximation by perfect complexes holds on every algebraic
space representable by an affine scheme. -/
@[stacks 08HM] #check
  (HasApproximationByPerfectComplexes.of_isAffine :
    ∀ {S : Scheme.{u}} (X : AlgebraicSpace S) [IsAffine X],
      HasApproximationByPerfectComplexes X)
