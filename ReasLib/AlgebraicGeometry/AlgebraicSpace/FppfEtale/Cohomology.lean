module

public import Mathlib.CategoryTheory.IsomorphismClasses
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import ReasLib.CategoryTheory.DerivedCategory.Functor.TotalRightDerived.Cochain
public import ReasLib.CategoryTheory.Sites.Derived.Sections
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSite.Cohomology.Restriction
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FppfEtale.InverseImage
import Mathlib.Tactic.CrossRefAttribute

/-!
# Fppf and étale cohomology of algebraic spaces

For an algebraic space `X` over a scheme `S`, étale cohomology of an abelian
sheaf `F` (resp. `K ∈ D⁺(X_étale)`) agrees with fppf cohomology of `a_X⁻¹ F`
(resp. `a_X⁻¹ K`).
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.FppfEtale
open CategoryTheory CategoryTheory.Limits
open CategoryTheory.GrothendieckTopology
open CategoryTheory.Sheaf
open CategoryTheory.Functor.RightDerived
open scoped GrothendieckTopologyDerivedSections

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.FppfEtale

/-- For an algebraic space `X` over a scheme `S` and an abelian
sheaf `F` on `X_étale`, étale cohomology `H^q(X_étale, F)` agrees with fppf
cohomology `H^q_fppf(X, a_X⁻¹ F)`. -/
@[stacks 0DGH]
theorem cohomology_aInverseImage {S : Scheme.{u}} {X : AlgebraicSpace S}
    (F : Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1}) (q : ℕ) :
    IsIsomorphic (etaleCohomology X F q)
      (((siteAbelianSectionsFunctor ((fppfTopology S).over X)
          (Over.mk (𝟙 X))).rightDerived q).obj ((aInverseAb X).obj F)) :=
  sorry

/-- For an algebraic space `X` over a scheme `S` and
`K ∈ D⁺(X_étale)`, étale hypercohomology `H^q(X_étale, K)` agrees with fppf
hypercohomology `H^q_fppf(X, a_X⁻¹ K)`. -/
@[stacks 0DGH]
theorem plusCohomology_aInverseImage {S : Scheme.{u}} {X : AlgebraicSpace S}
    (K : DerivedCategory.Plus (Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1}))
    (q : ℤ) :
    IsIsomorphic
      ((DerivedCategory.homologyFunctor AddCommGrpCat.{u + 1} q).obj
        ((Cochain.functor (globalSections X)).obj (DerivedCategory.Plus.ι.obj K)))
      ((DerivedCategory.homologyFunctor AddCommGrpCat.{u + 1} q).obj
        ((RΓ[(fppfTopology S).over X](Over.mk (𝟙 X))).obj
          (DerivedCategory.Plus.ι.obj ((aInverseAbPlus X).obj K)))) :=
  sorry

/-- Inverse image `a_X⁻¹` of the constant abelian sheaf on `X_étale` is isomorphic to
the constant abelian sheaf on `(Spaces/X)_fppf`. -/
theorem aInverseAb_obj_constantSheaf {S : Scheme.{u}} {X : AlgebraicSpace S}
    (A : AddCommGrpCat.{u + 1}) :
    IsIsomorphic
      ((aInverseAb X).obj
        ((constantSheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1}).obj A))
      ((constantSheaf ((fppfTopology S).over X) AddCommGrpCat.{u + 1}).obj A) :=
  sorry

/-- For an algebraic space `X` over a scheme `S` and an abelian
group `A`, étale cohomology of the constant sheaf with value `A` agrees with fppf
cohomology of the constant sheaf with value `A`. -/
@[stacks 0DGH]
theorem cohomology_constant {S : Scheme.{u}} {X : AlgebraicSpace S}
    (A : AddCommGrpCat.{u + 1}) (q : ℕ) :
    IsIsomorphic
      (etaleCohomology X
        ((constantSheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1}).obj A) q)
      (((siteAbelianSectionsFunctor ((fppfTopology S).over X)
          (Over.mk (𝟙 X))).rightDerived q).obj
        ((constantSheaf ((fppfTopology S).over X) AddCommGrpCat.{u + 1}).obj A)) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.FppfEtale

end

end
