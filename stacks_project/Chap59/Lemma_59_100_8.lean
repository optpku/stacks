module

public import stacks_project.Chap59.Lemma_59_100_7
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Fppf.EtaleCohomologyComparison
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.FppfEtale
open CategoryTheory.GrothendieckTopology
open CategoryTheory.Sheaf
open scoped GrothendieckTopologyDerivedSections

noncomputable section

universe u

/- Lemma 59.100.8 (1): for a scheme `X` and an abelian sheaf `F` on `X_étale`, étale
cohomology `H^q(X_étale, F)` agrees with fppf cohomology `H^q_fppf(X, a_X⁻¹ F)`. -/
@[stacks 0DDU] #check (AlgebraicGeometry.Scheme.FppfEtale.cohomology_aInverseImage :
  ∀ {X : Scheme.{u}}
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (q : ℕ),
    IsIsomorphic
      (((siteAbelianSectionsFunctor X.smallEtaleTopology (Etale.globalEtale X)).rightDerived q).obj F)
      (((siteAbelianSectionsFunctor (fppfTopology.over X)
          (Over.mk (𝟙 X))).rightDerived q).obj ((aInverseAb X).obj F)))

/- Lemma 59.100.8 (2): for a scheme `X` and `K ∈ D⁺(X_étale)`, étale hypercohomology
`H^q(X_étale, K)` agrees with fppf hypercohomology `H^q_fppf(X, a_X⁻¹ K)`. -/
@[stacks 0DDU] #check (AlgebraicGeometry.Scheme.FppfEtale.plusCohomology_aInverseImage :
  ∀ {X : Scheme.{u}}
    (K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}))
    (q : ℤ),
    IsIsomorphic
      ((DerivedCategory.homologyFunctor AddCommGrpCat.{u + 1} q).obj
        ((RΓ[X.smallEtaleTopology](Etale.globalEtale X)).obj (DerivedCategory.Plus.ι.obj K)))
      ((DerivedCategory.homologyFunctor AddCommGrpCat.{u + 1} q).obj
        ((RΓ[fppfTopology.over X](Over.mk (𝟙 X))).obj
          (DerivedCategory.Plus.ι.obj ((aInverseAbPlus X).obj K)))))

/- Lemma 59.100.8 (3): for a scheme `X` and an abelian group `A`, étale cohomology of
the constant sheaf with value `A` agrees with fppf cohomology of the constant sheaf
with value `A`. -/
@[stacks 0DDU] #check (AlgebraicGeometry.Scheme.FppfEtale.cohomology_constant :
  ∀ {X : Scheme.{u}}
    (A : AddCommGrpCat.{u + 1}) (q : ℕ),
    IsIsomorphic
      (((siteAbelianSectionsFunctor X.smallEtaleTopology (Etale.globalEtale X)).rightDerived q).obj
        ((constantSheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}).obj A))
      (((siteAbelianSectionsFunctor (fppfTopology.over X)
          (Over.mk (𝟙 X))).rightDerived q).obj
        ((constantSheaf (fppfTopology.over X) AddCommGrpCat.{u + 1}).obj A)))

end

end
