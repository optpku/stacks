module

public import Mathlib.CategoryTheory.IsomorphismClasses
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.GroupTheory.Torsion
public import ReasLib.CategoryTheory.DerivedCategory.CohomologyIn.Bounded
public import ReasLib.CategoryTheory.DerivedCategory.Functor.TotalRightDerived.Cochain
public import ReasLib.CategoryTheory.Sites.Derived.Sections
public import stacks_project.Chap84.Lemma_84_4_9_Comparison
public import stacks_project.Chap84.Lemma_84_8_1_InverseImage
public import stacks_project.Chap84.Lemma_84_8_2_Adjunction
import Mathlib.Tactic.CrossRefAttribute

/-!
# Lemma 84.8.3

For an algebraic space `X` over a scheme `S`, with
`a_X : Sh((Spaces/X)_ph) ⟶ Sh(X_étale)`, étale cohomology of a torsion abelian
sheaf `F` (resp. `K ∈ D⁺(X_étale)` with torsion cohomology sheaves) agrees with
ph cohomology of `a_X⁻¹ F` (resp. `a_X⁻¹ K`). If `A` is a torsion abelian group,
then `H^q_étale(X, underline{A}) = H^q_ph(X, underline{A})`.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.PhComparison
open CategoryTheory CategoryTheory.Limits
open CategoryTheory.GrothendieckTopology
open CategoryTheory.Sheaf
open CategoryTheory.Functor.RightDerived
open scoped GrothendieckTopologyDerivedSections

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.PhComparison

/-- The constant abelian sheaf of a torsion abelian group on the small étale site
of an algebraic space is locally torsion. -/
theorem constantSheaf_isLocallyTorsion {S : Scheme.{u}} {X : AlgebraicSpace S}
    (A : AddCommGrpCat.{u + 1}) (hA : AddMonoid.IsTorsion A) :
    ((constantSheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1}).obj A).IsLocallyTorsion :=
  sorry

/-- Inverse image `a_X⁻¹` of the constant abelian sheaf on `X_étale` is isomorphic to
the constant abelian sheaf on `(Spaces/X)_ph`. -/
theorem aInverseImage_obj_constantSheaf {S : Scheme.{u}} {X : AlgebraicSpace S}
    (A : AddCommGrpCat.{u + 1}) :
    IsIsomorphic
      ((aInverseImage X).obj
        ((constantSheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1}).obj A))
      ((constantSheaf (bigPhSite X) AddCommGrpCat.{u + 1}).obj A) :=
  sorry

/-- Lemma 84.8.3 (1): for an algebraic space `X` over a scheme `S` and a torsion
abelian sheaf `F` on `X_étale`, étale cohomology `H^q(X_étale, F)` agrees with
ph cohomology `H^q_ph(X, a_X⁻¹ F)`. -/
@[stacks 0DGV]
theorem cohomology_aInverseImage {S : Scheme.{u}} {X : AlgebraicSpace S}
    (F : Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1})
    (hF : F.IsLocallyTorsion) (q : ℕ) :
    IsIsomorphic (etaleCohomology X F q)
      (((siteAbelianSectionsFunctor (bigPhSite X)
          (Over.mk (𝟙 X))).rightDerived q).obj ((aInverseImage X).obj F)) :=
  sorry

/-- Lemma 84.8.3 (2): for an algebraic space `X` over a scheme `S` and
`K ∈ D⁺(X_étale)` with torsion cohomology sheaves, étale hypercohomology
`H^q(X_étale, K)` agrees with ph hypercohomology `H^q_ph(X, a_X⁻¹ K)`. -/
@[stacks 0DGV]
theorem plusCohomology_aInverseImage {S : Scheme.{u}} {X : AlgebraicSpace S}
    (K : DerivedCategory.Plus (Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1}))
    (hK : DerivedCategory.Plus.cohomologyIn (Sheaf.torsion (smallEtaleTopology X)) K)
    (q : ℤ) :
    IsIsomorphic
      ((DerivedCategory.homologyFunctor AddCommGrpCat.{u + 1} q).obj
        ((Cochain.functor (globalSections X)).obj (DerivedCategory.Plus.ι.obj K)))
      ((DerivedCategory.homologyFunctor AddCommGrpCat.{u + 1} q).obj
        ((RΓ[bigPhSite X](Over.mk (𝟙 X))).obj
          (DerivedCategory.Plus.ι.obj ((plusAInverseImage X).obj K)))) :=
  sorry

/-- Lemma 84.8.3 (3): for an algebraic space `X` over a scheme `S` and a torsion
abelian group `A`, étale cohomology of the constant sheaf with value `A` agrees
with ph cohomology of the constant sheaf with value `A`. -/
@[stacks 0DGV]
theorem cohomology_constant {S : Scheme.{u}} {X : AlgebraicSpace S}
    (A : AddCommGrpCat.{u + 1}) (hA : AddMonoid.IsTorsion A) (q : ℕ) :
    IsIsomorphic
      (etaleCohomology X
        ((constantSheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1}).obj A) q)
      (((siteAbelianSectionsFunctor (bigPhSite X) (Over.mk (𝟙 X))).rightDerived q).obj
        ((constantSheaf (bigPhSite X) AddCommGrpCat.{u + 1}).obj A)) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.PhComparison

end

end
