/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.ApproximationByPerfectComplexes
public import ReasLib.AlgebraicGeometry.Scheme.Module.Cohomology.AffineCover

@[expose] public section

open CategoryTheory
open TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.HasPerfectApproximation

/-- On an affine scheme, an `m`-pseudo-coherent quasicoherent derived object whose
cohomology is supported on a closed subset from degree `m - r + 1` onward has a perfect
approximation through degree `m` when the complement has an affine open cover indexed by
`Fin r`. -/
theorem of_isAffine {X : Scheme.{u}} [IsAffine X] (T : Closeds X)
    (E : DerivedCategory.CohomologyIn
      (RingedSpace.quasiCoherentModuleProperty X.toRingedSpace))
    (m : ℤ) (r : ℕ) (h_cover : AffineOpenCover.HasCard (T.compl : Scheme) r)
    (h_pseudoCoherent : RingedSpace.ModuleDerived.IsMPseudoCoherent E.obj m)
    (h_support : ∀ i : ℤ, m - (r : ℤ) + 1 ≤ i →
      RingedSpace.moduleSupportedOn (T : Set X)
        (RingedSpace.ModuleDerived.cohomologySheaf E.obj i)) :
    HasPerfectApproximation T E m := sorry

end AlgebraicGeometry.Scheme.HasPerfectApproximation

namespace AlgebraicGeometry.Scheme.HasApproximationByPerfectComplexes

/-- Every affine scheme admits approximation by perfect complexes. -/
theorem of_isAffine (X : Scheme.{u}) [IsAffine X] :
    HasApproximationByPerfectComplexes X := sorry

end AlgebraicGeometry.Scheme.HasApproximationByPerfectComplexes
