/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap59.Lemma_59_100_7
public import stacks_project.Chap59.Lemma_59_39_1
public import ReasLib.CategoryTheory.Sites.Derived.Sections
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.FppfEtale
open CategoryTheory.GrothendieckTopology
open CategoryTheory.Sheaf
open scoped GrothendieckTopologyDerivedSections

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.FppfEtale

/-- Lemma 59.100.8 (1): for a scheme `X` and an abelian sheaf `F` on `X_étale`, étale
cohomology `H^q(X_étale, F)` agrees with fppf cohomology `H^q_fppf(X, a_X⁻¹ F)`. -/
@[stacks 0DDU]
theorem cohomology_aInverseImage {X : Scheme.{u}}
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (q : ℕ) :
    IsIsomorphic
      (((siteAbelianSectionsFunctor X.smallEtaleTopology (globalEtale X)).rightDerived q).obj F)
      (((siteAbelianSectionsFunctor (fppfTopology.over X)
          (Over.mk (𝟙 X))).rightDerived q).obj ((aInverseAb X).obj F)) := sorry

/-- Lemma 59.100.8 (2): for a scheme `X` and `K ∈ D⁺(X_étale)`, étale hypercohomology
`H^q(X_étale, K)` agrees with fppf hypercohomology `H^q_fppf(X, a_X⁻¹ K)`. -/
@[stacks 0DDU]
theorem plusCohomology_aInverseImage {X : Scheme.{u}}
    (K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}))
    (q : ℤ) :
    IsIsomorphic
      ((DerivedCategory.homologyFunctor AddCommGrpCat.{u + 1} q).obj
        ((RΓ[X.smallEtaleTopology](globalEtale X)).obj (DerivedCategory.Plus.ι.obj K)))
      ((DerivedCategory.homologyFunctor AddCommGrpCat.{u + 1} q).obj
        ((RΓ[fppfTopology.over X](Over.mk (𝟙 X))).obj
          (DerivedCategory.Plus.ι.obj ((aInverseAbPlus X).obj K)))) := sorry

/-- Inverse image `a_X⁻¹` of the constant abelian sheaf on `X_étale` is isomorphic to
the constant abelian sheaf on `(Sch/X)_fppf`. -/
theorem aInverseAb_obj_constantSheaf {X : Scheme.{u}} (A : AddCommGrpCat.{u + 1}) :
    IsIsomorphic
      ((aInverseAb X).obj
        ((constantSheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}).obj A))
      ((constantSheaf (fppfTopology.over X) AddCommGrpCat.{u + 1}).obj A) := sorry

/-- Lemma 59.100.8 (3): for a scheme `X` and an abelian group `A`, étale cohomology of
the constant sheaf with value `A` agrees with fppf cohomology of the constant sheaf
with value `A`. -/
@[stacks 0DDU]
theorem cohomology_constant {X : Scheme.{u}}
    (A : AddCommGrpCat.{u + 1}) (q : ℕ) :
    IsIsomorphic
      (((siteAbelianSectionsFunctor X.smallEtaleTopology (globalEtale X)).rightDerived q).obj
        ((constantSheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}).obj A))
      (((siteAbelianSectionsFunctor (fppfTopology.over X)
          (Over.mk (𝟙 X))).rightDerived q).obj
        ((constantSheaf (fppfTopology.over X) AddCommGrpCat.{u + 1}).obj A)) :=
    sorry

end AlgebraicGeometry.Scheme.FppfEtale

end

end
