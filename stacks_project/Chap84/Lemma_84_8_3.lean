module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Ph.Cohomology
import StacksCheckRecall

/-!
# Lemma 84.8.3

For an algebraic space `X` over a scheme `S`, with
`a_X : Sh((Spaces/X)_ph) ⟶ Sh(X_étale)`, étale cohomology of a torsion abelian
sheaf `F` (resp. `K ∈ D⁺(X_étale)` with torsion cohomology sheaves) agrees with
ph cohomology of `a_X⁻¹ F` (resp. `a_X⁻¹ K`). If `A` is a torsion abelian group,
then `H^q_étale(X, underline{A}) = H^q_ph(X, underline{A})`.
-/

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.PhComparison
open CategoryTheory CategoryTheory.Limits
open CategoryTheory.GrothendieckTopology
open CategoryTheory.Sheaf
open CategoryTheory.Functor.RightDerived
open scoped GrothendieckTopologyDerivedSections

universe u

/- Lemma 84.8.3 (1): étale and ph cohomology agree for locally torsion abelian sheaves. -/
@[stacks 0DGV] #check (AlgebraicGeometry.AlgebraicSpace.PhComparison.cohomology_aInverseImage :
  ∀ {S : Scheme.{u}} {X : AlgebraicSpace S}
    (F : Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1})
    (hF : F.IsLocallyTorsion) (q : ℕ),
    IsIsomorphic (etaleCohomology X F q)
      (((siteAbelianSectionsFunctor (bigPhSite X)
          (Over.mk (𝟙 X))).rightDerived q).obj ((aInverseImage X).obj F)))

/- Lemma 84.8.3 (2): étale and ph hypercohomology agree for bounded-below complexes
with torsion cohomology sheaves. -/
@[stacks 0DGV] #check (AlgebraicGeometry.AlgebraicSpace.PhComparison.plusCohomology_aInverseImage :
  ∀ {S : Scheme.{u}} {X : AlgebraicSpace S}
    (K : DerivedCategory.Plus (Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1}))
    (hK : DerivedCategory.Plus.cohomologyIn (Sheaf.torsion (smallEtaleTopology X)) K)
    (q : ℤ),
    IsIsomorphic
      ((DerivedCategory.homologyFunctor AddCommGrpCat.{u + 1} q).obj
        ((Cochain.functor (globalSections X)).obj (DerivedCategory.Plus.ι.obj K)))
      ((DerivedCategory.homologyFunctor AddCommGrpCat.{u + 1} q).obj
        ((RΓ[bigPhSite X](Over.mk (𝟙 X))).obj
          (DerivedCategory.Plus.ι.obj ((plusAInverseImage X).obj K)))))

/- Lemma 84.8.3 (3): étale and ph cohomology agree for constant torsion coefficients. -/
@[stacks 0DGV] #check (AlgebraicGeometry.AlgebraicSpace.PhComparison.cohomology_constant :
  ∀ {S : Scheme.{u}} {X : AlgebraicSpace S}
    (A : AddCommGrpCat.{u + 1}) (hA : AddMonoid.IsTorsion A) (q : ℕ),
    IsIsomorphic
      (etaleCohomology X
        ((constantSheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1}).obj A) q)
      (((siteAbelianSectionsFunctor (bigPhSite X) (Over.mk (𝟙 X))).rightDerived q).obj
        ((constantSheaf (bigPhSite X) AddCommGrpCat.{u + 1}).obj A)))
