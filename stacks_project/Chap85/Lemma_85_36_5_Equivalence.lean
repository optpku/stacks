/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.DerivedCategory.CohomologyIn.Bounded
public import stacks_project.Chap85.Lemma_85_33_2_Cartesian
public import stacks_project.Chap85.Lemma_85_33_3_Adjunction
public import stacks_project.Chap85.Lemma_85_36_2_Hypercovering
public import stacks_project.Chap85.Lemma_85_36_3

/-!
# Derived cartesian equivalence data for proper hypercoverings

If `a : U ⟶ X` is a proper hypercovering, the bounded-below derived inverse image
`a⁻¹` corestricts to `D⁺` objects with cartesian cohomology on `U_étale`, and
`Ra_*` is a quasi-inverse on that full subcategory.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace.Simplicial
open Functor
open scoped Simplicial

noncomputable section

namespace AlgebraicGeometry.AlgebraicSpace.Simplicial

variable {S : Scheme.{u}} {X : AlgebraicSpace S}
variable {U : SimplicialObject (AlgebraicSpace S)}
variable (a : U ⟶ (const SimplexCategoryᵒᵖ).obj X)

/-- Derived inverse image `a⁻¹` sends every object of `D⁺(X_étale)` to an object of
`D⁺(U_étale)` whose cohomology sheaves are cartesian. -/
theorem plusInverseImage_mem_cohomologyIn
    (K : DerivedCategory.Plus (Sheaf (spacesEtaleTopology X) AddCommGrpCat.{u + 1})) :
    DerivedCategory.Plus.cohomologyIn (cartesianProperty U AddCommGrpCat.{u + 1})
      ((plusInverseImage a).obj K) :=
  sorry

/-- The functor `a⁻¹` corestricted to `D⁺` objects with cartesian cohomology. -/
def properPlusCartesianFunctor :
    DerivedCategory.Plus (Sheaf (spacesEtaleTopology X) AddCommGrpCat.{u + 1}) ⥤
      DerivedCategory.Plus.CohomologyIn (cartesianProperty U AddCommGrpCat.{u + 1}) :=
  (DerivedCategory.Plus.cohomologyIn (cartesianProperty U AddCommGrpCat.{u + 1})).lift
    (plusInverseImage a) (plusInverseImage_mem_cohomologyIn a)

/-- On objects, `properPlusCartesianFunctor` is derived inverse image along the
spaces-étale augmentation. -/
theorem properPlusCartesianFunctor_obj
    (K : DerivedCategory.Plus (Sheaf (spacesEtaleTopology X) AddCommGrpCat.{u + 1})) :
    ((properPlusCartesianFunctor a).obj K).obj = (plusInverseImage a).obj K :=
  sorry

/-- The functor sending a `D⁺` object with cartesian cohomology to `Ra_*` of its
underlying object. -/
def properPlusCartesianInverse :
    DerivedCategory.Plus.CohomologyIn (cartesianProperty U AddCommGrpCat.{u + 1}) ⥤
      DerivedCategory.Plus (Sheaf (spacesEtaleTopology X) AddCommGrpCat.{u + 1}) :=
  (DerivedCategory.Plus.cohomologyIn (cartesianProperty U AddCommGrpCat.{u + 1})).ι ⋙
    plusDirectImage a

/-- On objects, `properPlusCartesianInverse` is derived direct image along the
spaces-étale augmentation. -/
theorem properPlusCartesianInverse_obj
    (K : DerivedCategory.Plus.CohomologyIn
      (cartesianProperty U AddCommGrpCat.{u + 1})) :
    (properPlusCartesianInverse a).obj K = (plusDirectImage a).obj K.obj :=
  sorry

/-- The derived counit of `a⁻¹ ⊣ Ra_*` is an isomorphism on `D⁺` objects with
cartesian cohomology, when `a` is a proper hypercovering. -/
theorem properPlusDerivedCounit_app_isIso (ha : IsProperHypercovering a)
    (K : DerivedCategory.Plus.CohomologyIn
      (cartesianProperty U AddCommGrpCat.{u + 1})) :
    IsIso ((plusAdjunction a).counit.app K.obj) :=
  sorry

/-- The unit isomorphism `𝟭 ≅ a⁻¹ ⋙ Ra_*` of proper hypercovering descent on
`D⁺(X_étale)`. -/
def properPlusCartesianUnitIso (ha : IsProperHypercovering a) :
    𝟭 (DerivedCategory.Plus (Sheaf (spacesEtaleTopology X) AddCommGrpCat.{u + 1})) ≅
      properPlusCartesianFunctor a ⋙ properPlusCartesianInverse a :=
  @asIso _ _ _ _ (plusDerivedUnit a) (properPlusDerivedUnit_isIso a ha)

/-- The component of `properPlusCartesianUnitIso` at `K` is the derived unit. -/
theorem properPlusCartesianUnitIso_hom_app (ha : IsProperHypercovering a)
    (K : DerivedCategory.Plus (Sheaf (spacesEtaleTopology X) AddCommGrpCat.{u + 1})) :
    (properPlusCartesianUnitIso a ha).hom.app K = (plusDerivedUnit a).app K :=
  sorry

/-- Naturality of the counit components of proper-hypercovering descent on `D⁺`
objects with cartesian cohomology. -/
theorem properPlusCartesianCounitIso_naturality (ha : IsProperHypercovering a)
    {K L : DerivedCategory.Plus.CohomologyIn
      (cartesianProperty U AddCommGrpCat.{u + 1})} (f : K ⟶ L) :
    (properPlusCartesianInverse a ⋙ properPlusCartesianFunctor a).map f ≫
        ((DerivedCategory.Plus.cohomologyIn
            (cartesianProperty U AddCommGrpCat.{u + 1})).isoMk
          (@asIso _ _ _ _ ((plusAdjunction a).counit.app L.obj)
            (properPlusDerivedCounit_app_isIso a ha L))).hom =
      ((DerivedCategory.Plus.cohomologyIn
            (cartesianProperty U AddCommGrpCat.{u + 1})).isoMk
          (@asIso _ _ _ _ ((plusAdjunction a).counit.app K.obj)
            (properPlusDerivedCounit_app_isIso a ha K))).hom ≫
        (𝟭 (DerivedCategory.Plus.CohomologyIn
            (cartesianProperty U AddCommGrpCat.{u + 1}))).map f :=
  sorry

/-- The counit isomorphism `Ra_* ⋙ a⁻¹ ≅ 𝟭` on `D⁺` objects with cartesian
cohomology. -/
def properPlusCartesianCounitIso (ha : IsProperHypercovering a) :
    properPlusCartesianInverse a ⋙ properPlusCartesianFunctor a ≅
      𝟭 (DerivedCategory.Plus.CohomologyIn
        (cartesianProperty U AddCommGrpCat.{u + 1})) :=
  NatIso.ofComponents
    (fun K ↦
      (DerivedCategory.Plus.cohomologyIn
          (cartesianProperty U AddCommGrpCat.{u + 1})).isoMk
        (@asIso _ _ _ _ ((plusAdjunction a).counit.app K.obj)
          (properPlusDerivedCounit_app_isIso a ha K)))
    (fun f ↦ properPlusCartesianCounitIso_naturality a ha f)

/-- The underlying morphism of `properPlusCartesianCounitIso` at `K` is the derived
counit on the underlying object of `D⁺(U_étale)`. -/
theorem properPlusCartesianCounitIso_hom_app_hom (ha : IsProperHypercovering a)
    (K : DerivedCategory.Plus.CohomologyIn
      (cartesianProperty U AddCommGrpCat.{u + 1})) :
    ((properPlusCartesianCounitIso a ha).hom.app K).hom =
      (plusAdjunction a).counit.app K.obj :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Simplicial

end
