/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap59.Lemma_59_103_6
public import stacks_project.Chap59.Lemma_59_39_1
public import ReasLib.CategoryTheory.Sites.Derived.Sections
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.GroupTheory.Torsion
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.HComparison
open CategoryTheory.GrothendieckTopology
open CategoryTheory.Sheaf
open scoped GrothendieckTopologyDerivedSections

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.HComparison

/-- The constant abelian sheaf on the small étale site of a torsion abelian group is
locally torsion. -/
theorem constantSheaf_isLocallyTorsion {X : Scheme.{u}}
    (A : AddCommGrpCat.{u + 1}) (hA : AddMonoid.IsTorsion A) :
    ((constantSheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}).obj A).IsLocallyTorsion :=
  sorry

/-- Lemma 59.103.7 (1): for a scheme `X` and a torsion abelian sheaf `F` on `X_étale`,
étale cohomology `H^q(X_étale, F)` agrees with h-cohomology `H^q_h(X, a_X⁻¹ F)`. -/
@[stacks 0EWH]
theorem cohomology_aInverseImage {X : Scheme.{u}}
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (hF : F.IsLocallyTorsion) (q : ℕ) :
    IsIsomorphic
      (((siteAbelianSectionsFunctor X.smallEtaleTopology (globalEtale X)).rightDerived q).obj F)
      (((siteAbelianSectionsFunctor (hPrecoverage.toGrothendieck.over X)
          (Over.mk (𝟙 X))).rightDerived q).obj ((aInverseImage X).obj F)) := sorry

/-- Lemma 59.103.7 (2): for a scheme `X` and `K ∈ D⁺(X_étale)` with torsion cohomology
sheaves, étale hypercohomology `H^q(X_étale, K)` agrees with h-hypercohomology
`H^q_h(X, a_X⁻¹ K)`. -/
@[stacks 0EWH]
theorem plusCohomology_aInverseImage {X : Scheme.{u}}
    (K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}))
    (hK : DerivedCategory.Plus.cohomologyIn (Sheaf.torsion X.smallEtaleTopology) K)
    (q : ℤ) :
    IsIsomorphic
      ((DerivedCategory.homologyFunctor AddCommGrpCat.{u + 1} q).obj
        ((RΓ[X.smallEtaleTopology](globalEtale X)).obj (DerivedCategory.Plus.ι.obj K)))
      ((DerivedCategory.homologyFunctor AddCommGrpCat.{u + 1} q).obj
        ((RΓ[hPrecoverage.toGrothendieck.over X](Over.mk (𝟙 X))).obj
          (DerivedCategory.Plus.ι.obj ((plusAInverseImage X).obj K)))) := sorry

/-- Lemma 59.103.7 (3): for a scheme `X` and a torsion abelian group `A`, étale
cohomology of the constant sheaf with value `A` agrees with h-cohomology of
the constant sheaf with value `A`. -/
@[stacks 0EWH]
theorem cohomology_constant {X : Scheme.{u}}
    (A : AddCommGrpCat.{u + 1}) (hA : AddMonoid.IsTorsion A) (q : ℕ) :
    IsIsomorphic
      (((siteAbelianSectionsFunctor X.smallEtaleTopology (globalEtale X)).rightDerived q).obj
        ((constantSheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}).obj A))
      (((siteAbelianSectionsFunctor (hPrecoverage.toGrothendieck.over X)
          (Over.mk (𝟙 X))).rightDerived q).obj
        ((constantSheaf (hPrecoverage.toGrothendieck.over X) AddCommGrpCat.{u + 1}).obj A)) :=
    sorry

end AlgebraicGeometry.Scheme.HComparison

end

end
