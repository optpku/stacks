/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.AffineOpenCover
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.ApproximationByPerfectComplexes

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace

universe u

namespace AlgebraicGeometry.AlgebraicSpace

namespace HasPerfectApproximation

/-- On an affine algebraic space, an m-pseudo-coherent object of DerivedQCoh
whose cohomology is supported on T from degree m - r + 1 onward has a perfect
approximation through degree m when the complement of T is a union of r affine
opens. -/
theorem of_isAffine {S : Scheme.{u}} {X : AlgebraicSpace S} [IsAffine X]
    (T : Closeds (Points X)) (E : DerivedQCoh X) (m : ℤ) (r : ℕ)
    (h_cover : AffineOpenCover.HasCard (OpenSubspace.fromOpens T.compl).X r)
    (h_pseudoCoherent : IsMPseudoCoherent X E.obj m)
    (h_support : ∀ i : ℤ, m - (r : ℤ) + 1 ≤ i →
      Modules.moduleSupportedOn (T : Set (Points X))
        ((DerivedCategory.homologyFunctor (Modules X) i).obj E.obj)) :
    HasPerfectApproximation T E m := sorry

end HasPerfectApproximation

namespace HasApproximationByPerfectComplexes

/-- Every affine algebraic space admits approximation by perfect complexes. -/
theorem of_isAffine {S : Scheme.{u}} (X : AlgebraicSpace S) [IsAffine X] :
    HasApproximationByPerfectComplexes X := sorry

end HasApproximationByPerfectComplexes

end AlgebraicGeometry.AlgebraicSpace
