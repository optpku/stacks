module

public import ReasLib.CategoryTheory.DerivedCategory.CohomologyIn.Bounded
public import ReasLib.CategoryTheory.ObjectProperty.WeakSerre
public import stacks_project.Chap85.Lemma_85_33_2_Cartesian
public import stacks_project.Chap85.Lemma_85_33_2_Hypercovering
public import stacks_project.Chap85.Lemma_85_33_3
public import stacks_project.Chap85.Lemma_85_33_3_Adjunction

/-!
# Bounded-below cartesian derived functors of a spaces-étale augmentation

The exact inverse image `a⁻¹` corestricts to `D_A⁺(U_étale)`, the full subcategory of
`D⁺(U_étale)` whose cohomology lies in the cartesian abelian sheaves, and `Ra_*` is
defined on that subcategory. When `a` is an fppf hypercovering these functors are
inverse equivalences.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open DerivedCategory.TStructure
open Functor
open scoped Simplicial

noncomputable section

namespace AlgebraicGeometry.AlgebraicSpace.Simplicial

variable {S : Scheme.{u}} (U : SimplicialObject (AlgebraicSpace S))

/-- Cartesian abelian sheaves on `U_étale` form a weak Serre subcategory of
`Ab(U_étale)`, as recorded for this spaces-étale cartesian property by Lemma 85.12.6. -/
instance cartesianProperty_addCommGrp_isWeakSerreClass :
    ObjectProperty.IsWeakSerreClass (cartesianProperty U AddCommGrpCat.{u + 1}) :=
  sorry

variable {U}
variable {X : AlgebraicSpace S} (a : U ⟶ (const SimplexCategoryᵒᵖ).obj X)

/-- Derived inverse image `a⁻¹` sends `D⁺(X_étale)` into objects whose cohomology is
cartesian on `U_étale`. -/
theorem plusInverseImage_mem_cohomologyIn
    (K : DerivedCategory.Plus (Sheaf (spacesEtaleTopology X) AddCommGrpCat.{u + 1})) :
    DerivedCategory.Plus.cohomologyIn (cartesianProperty U AddCommGrpCat.{u + 1})
      ((plusInverseImage a).obj K) :=
  sorry

/-- The functor `a⁻¹` corestricted from `D⁺(X_étale)` to `D_A⁺(U_étale)`, where `A`
is the object property of cartesian abelian sheaves on `U_étale`. -/
def plusCartesianFunctor :
    DerivedCategory.Plus (Sheaf (spacesEtaleTopology X) AddCommGrpCat.{u + 1}) ⥤
      DerivedCategory.Plus.CohomologyIn
        (cartesianProperty U AddCommGrpCat.{u + 1}) :=
  (DerivedCategory.Plus.cohomologyIn
      (cartesianProperty U AddCommGrpCat.{u + 1})).lift
    (plusInverseImage a) (plusInverseImage_mem_cohomologyIn a)

/-- On objects, `plusCartesianFunctor` is derived inverse image along the spaces-étale
augmentation. -/
theorem plusCartesianFunctor_obj
    (K : DerivedCategory.Plus (Sheaf (spacesEtaleTopology X) AddCommGrpCat.{u + 1})) :
    ((plusCartesianFunctor a).obj K).obj = (plusInverseImage a).obj K :=
  sorry

/-- The functor sending an object of `D_A⁺(U_étale)` to `Ra_*` of its underlying
object of `D⁺(U_étale)`. -/
def plusCartesianInverse :
    DerivedCategory.Plus.CohomologyIn
        (cartesianProperty U AddCommGrpCat.{u + 1}) ⥤
      DerivedCategory.Plus (Sheaf (spacesEtaleTopology X) AddCommGrpCat.{u + 1}) :=
  (DerivedCategory.Plus.cohomologyIn
      (cartesianProperty U AddCommGrpCat.{u + 1})).ι ⋙
    plusDirectImage a

/-- On objects, `plusCartesianInverse` is derived direct image along the spaces-étale
augmentation. -/
theorem plusCartesianInverse_obj
    (G : DerivedCategory.Plus.CohomologyIn
      (cartesianProperty U AddCommGrpCat.{u + 1})) :
    (plusCartesianInverse a).obj G = (plusDirectImage a).obj G.obj :=
  sorry

/-- Forgetting cartesian cohomology after `plusCartesianFunctor` recovers derived
inverse image, then `Ra_*`. -/
def plusCartesianFunctorCompInverseIso :
    plusCartesianFunctor a ⋙ plusCartesianInverse a ≅
      plusInverseImage a ⋙ plusDirectImage a :=
  isoWhiskerRight
    ((DerivedCategory.Plus.cohomologyIn
        (cartesianProperty U AddCommGrpCat.{u + 1})).liftCompιIso
      (plusInverseImage a) (plusInverseImage_mem_cohomologyIn a))
    (plusDirectImage a)

/-- The underlying morphism of the derived unit in `D(X_étale)` is an isomorphism. -/
theorem plusDerivedUnit_app_hom_isIso (ha : IsFppfHypercovering a)
    (K : DerivedCategory.Plus (Sheaf (spacesEtaleTopology X) AddCommGrpCat.{u + 1})) :
    IsIso ((plusDerivedUnit a).app K).hom :=
  sorry

/-- The derived unit `𝟭 ⟶ a⁻¹ ⋙ Ra_*` as an isomorphism of functors on `D⁺(X_étale)`. -/
def plusDerivedUnitIso (ha : IsFppfHypercovering a) :
    𝟭 (DerivedCategory.Plus (Sheaf (spacesEtaleTopology X) AddCommGrpCat.{u + 1})) ≅
      plusInverseImage a ⋙ plusDirectImage a :=
  NatIso.ofComponents
    (fun K ↦
      t.plus.isoMk
        (@asIso _ _ _ _ ((plusDerivedUnit a).app K).hom
          (plusDerivedUnit_app_hom_isIso a ha K)))
    sorry

/-- The unit isomorphism `𝟭 ≅ a⁻¹ ⋙ Ra_*` on `D⁺(X_étale)`, corestricted to
`D_A⁺(U_étale)`. -/
def plusCartesianUnitIso (ha : IsFppfHypercovering a) :
    𝟭 (DerivedCategory.Plus (Sheaf (spacesEtaleTopology X) AddCommGrpCat.{u + 1})) ≅
      plusCartesianFunctor a ⋙ plusCartesianInverse a :=
  (plusDerivedUnitIso a ha).trans (plusCartesianFunctorCompInverseIso a).symm

/-- The component of `plusCartesianUnitIso` at `K` is the derived adjunction unit. -/
theorem plusCartesianUnitIso_hom_app (ha : IsFppfHypercovering a)
    (K : DerivedCategory.Plus (Sheaf (spacesEtaleTopology X) AddCommGrpCat.{u + 1})) :
    (plusCartesianUnitIso a ha).hom.app K = (plusDerivedUnit a).app K :=
  sorry

/-- The derived adjunction counit is an isomorphism on objects of `D_A⁺(U_étale)`. -/
theorem plusAdjunction_counit_app_isIso (ha : IsFppfHypercovering a)
    (G : DerivedCategory.Plus.CohomologyIn
      (cartesianProperty U AddCommGrpCat.{u + 1})) :
    IsIso ((plusAdjunction a).counit.app G.obj) :=
  sorry

/-- Naturality of the counit components of the bounded-below cartesian derived
equivalence. -/
theorem plusCartesianCounitIso_naturality (ha : IsFppfHypercovering a)
    {F G : DerivedCategory.Plus.CohomologyIn
      (cartesianProperty U AddCommGrpCat.{u + 1})} (f : F ⟶ G) :
    (plusCartesianInverse a ⋙ plusCartesianFunctor a).map f ≫
        ((DerivedCategory.Plus.cohomologyIn
            (cartesianProperty U AddCommGrpCat.{u + 1})).isoMk
          (@asIso _ _ _ _ ((plusAdjunction a).counit.app G.obj)
            (plusAdjunction_counit_app_isIso a ha G))).hom =
      ((DerivedCategory.Plus.cohomologyIn
            (cartesianProperty U AddCommGrpCat.{u + 1})).isoMk
          (@asIso _ _ _ _ ((plusAdjunction a).counit.app F.obj)
            (plusAdjunction_counit_app_isIso a ha F))).hom ≫
        (𝟭 (DerivedCategory.Plus.CohomologyIn
            (cartesianProperty U AddCommGrpCat.{u + 1}))).map f :=
  sorry

/-- The counit isomorphism `Ra_* ⋙ a⁻¹ ≅ 𝟭` on `D_A⁺(U_étale)`. -/
def plusCartesianCounitIso (ha : IsFppfHypercovering a) :
    plusCartesianInverse a ⋙ plusCartesianFunctor a ≅
      𝟭 (DerivedCategory.Plus.CohomologyIn
        (cartesianProperty U AddCommGrpCat.{u + 1})) :=
  NatIso.ofComponents
    (fun G ↦
      (DerivedCategory.Plus.cohomologyIn
          (cartesianProperty U AddCommGrpCat.{u + 1})).isoMk
        (@asIso _ _ _ _ ((plusAdjunction a).counit.app G.obj)
          (plusAdjunction_counit_app_isIso a ha G)))
    (fun f ↦ plusCartesianCounitIso_naturality a ha f)

/-- The component of `plusCartesianCounitIso` at `G` is the derived adjunction counit
on the underlying object of `G`. -/
theorem plusCartesianCounitIso_hom_app (ha : IsFppfHypercovering a)
    (G : DerivedCategory.Plus.CohomologyIn
      (cartesianProperty U AddCommGrpCat.{u + 1})) :
    ((plusCartesianCounitIso a ha).hom.app G).hom =
      (plusAdjunction a).counit.app G.obj :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Simplicial

end
