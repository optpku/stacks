module

public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.CategoryTheory.DerivedCategory.CohomologyIn.Bounded
public import ReasLib.CategoryTheory.ObjectProperty.WeakSerre
public import stacks_project.Chap85.Lemma_85_17_1_Cartesian
public import stacks_project.Chap85.Lemma_85_17_3_Adjunction

/-!
# Lemma 85.17.5

Let `C` be a site with equalizers and fibre products, and let `K` be a
hypercovering. If `A` is the weak Serre subcategory of cartesian abelian sheaves on
`(C / K)_total`, then `a⁻¹` implements an equivalence `D⁺(C) ≌ D_A⁺((C / K)_total)`
with quasi-inverse `Ra_*`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.ObjectProperty
open Functor
open scoped SemiRepresentableFamily Simplicial

noncomputable section

universe w v u

namespace CategoryTheory.SemiRepresentableFamily

variable {C : Type u} [Category.{v} C]
variable (J : GrothendieckTopology C)
variable [h_eq : HasEqualizers C] [h_pb : HasPullbacks C]
include h_eq h_pb
variable (K : HypercoveringOf.Terminal.{w} J)
variable [HasSheafify J AddCommGrpCat.{max w u v}]
variable [HasSheafify (overSiteTotalTopology J K.simplicial) AddCommGrpCat.{max w u v}]
variable [∀ n : SimplexCategoryᵒᵖ,
    HasWeakSheafify (overSitePrecoverage J K.simplicial n).toGrothendieck
      AddCommGrpCat.{max w u v}]
variable [∀ n : SimplexCategoryᵒᵖ,
    HasWeakSheafify (overSitePrecoverage J K.simplicial n).toGrothendieck
      (Type (max w u v))]
variable [HasWeakSheafify (overSiteTotalTopology J K.simplicial) (Type (max w u v))]
variable [∀ P : (Grothendieck (overSiteDiagram K.simplicial))ᵒᵖ ⥤ AddCommGrpCat.{max w u v},
    (totalForget K.simplicial).op.HasPointwiseRightKanExtension P]
variable [(directImage J K.simplicial AddCommGrpCat.{max w u v}).toBoundedBelowDerived.HasRightDerivedFunctor
    (HomotopyCategory.Plus.quasiIso
      (Sheaf (overSiteTotalTopology J K.simplicial) AddCommGrpCat.{max w u v}))]

/-- Cartesian abelian sheaves on `(C / K)_total` form a weak Serre subcategory of
`Ab((C / K)_total)`. -/
instance cartesianProperty_isWeakSerreClass :
    IsWeakSerreClass
      (cartesianProperty J K.simplicial AddCommGrpCat.{max w u v}) :=
  sorry

/-- Derived inverse image `a⁻¹` sends every object of `D⁺(C)` to an object of
`D⁺((C / K)_total)` whose cohomology sheaves are cartesian. -/
theorem plusInverseImageDerived_cohomologyIn
    (E : DerivedCategory.Plus (Sheaf J AddCommGrpCat.{max w u v})) :
    DerivedCategory.Plus.cohomologyIn
      (cartesianProperty J K.simplicial AddCommGrpCat.{max w u v})
      ((plusInverseImageDerived J K).obj E) :=
  sorry

/-- The functor `a⁻¹` corestricted from `D⁺(C)` to `D_A⁺((C / K)_total)`, where `A`
is the object property of cartesian abelian sheaves. -/
def plusCartesianFunctor :
    DerivedCategory.Plus (Sheaf J AddCommGrpCat.{max w u v}) ⥤
      DerivedCategory.Plus.CohomologyIn
        (cartesianProperty J K.simplicial AddCommGrpCat.{max w u v}) :=
  (DerivedCategory.Plus.cohomologyIn
      (cartesianProperty J K.simplicial AddCommGrpCat.{max w u v})).lift
    (plusInverseImageDerived J K) (plusInverseImageDerived_cohomologyIn J K)

/-- The functor sending an object of `D_A⁺((C / K)_total)` to `Ra_*` of its
underlying object of `D⁺((C / K)_total)`. -/
def plusCartesianInverse :
    DerivedCategory.Plus.CohomologyIn
        (cartesianProperty J K.simplicial AddCommGrpCat.{max w u v}) ⥤
      DerivedCategory.Plus (Sheaf J AddCommGrpCat.{max w u v}) :=
  (DerivedCategory.Plus.cohomologyIn
      (cartesianProperty J K.simplicial AddCommGrpCat.{max w u v})).ι ⋙
    plusDirectImageDerived J K

/-- Forgetting the cartesian-cohomology condition recovers `a⁻¹` on `D⁺`. -/
theorem plusCartesianFunctor_comp_ι :
    plusCartesianFunctor J K ⋙
      (DerivedCategory.Plus.cohomologyIn
        (cartesianProperty J K.simplicial AddCommGrpCat.{max w u v})).ι =
      plusInverseImageDerived J K :=
  sorry

/-- The derived adjunction counit is an isomorphism on objects of
`D_A⁺((C / K)_total)`. -/
theorem plusDerivedCounit_app_isIso_of_cohomologyIn
    (E : DerivedCategory.Plus.CohomologyIn
      (cartesianProperty J K.simplicial AddCommGrpCat.{max w u v})) :
    IsIso ((plusDerivedAdjunction J K).counit.app E.obj) :=
  sorry

/-- Naturality of the unit components of the bounded-below cartesian derived
equivalence. -/
theorem plusCartesianUnitIso_naturality
    {E F : DerivedCategory.Plus (Sheaf J AddCommGrpCat.{max w u v})} (f : E ⟶ F) :
    (𝟭 (DerivedCategory.Plus (Sheaf J AddCommGrpCat.{max w u v}))).map f ≫
        (@asIso _ _ _ _ ((plusDerivedUnit J K).app F)
          (plusDerivedUnit_app_isIso J K F)).hom =
      (@asIso _ _ _ _ ((plusDerivedUnit J K).app E)
          (plusDerivedUnit_app_isIso J K E)).hom ≫
        (plusCartesianFunctor J K ⋙ plusCartesianInverse J K).map f :=
  sorry

/-- The unit isomorphism `𝟭 ≅ a⁻¹ ⋙ Ra_*` on `D⁺(C)`. -/
def plusCartesianUnitIso :
    𝟭 (DerivedCategory.Plus (Sheaf J AddCommGrpCat.{max w u v})) ≅
      plusCartesianFunctor J K ⋙ plusCartesianInverse J K :=
  NatIso.ofComponents
    (fun E ↦
      @asIso _ _ _ _ ((plusDerivedUnit J K).app E)
        (plusDerivedUnit_app_isIso J K E))
    (fun f ↦ plusCartesianUnitIso_naturality J K f)

/-- The component of `plusCartesianUnitIso` at `E` is the derived adjunction unit. -/
theorem plusCartesianUnitIso_hom_app
    (E : DerivedCategory.Plus (Sheaf J AddCommGrpCat.{max w u v})) :
    (plusCartesianUnitIso J K).hom.app E = (plusDerivedUnit J K).app E :=
  sorry

/-- Naturality of the counit components of the bounded-below cartesian derived
equivalence. -/
theorem plusCartesianCounitIso_naturality
    {E F : DerivedCategory.Plus.CohomologyIn
      (cartesianProperty J K.simplicial AddCommGrpCat.{max w u v})} (f : E ⟶ F) :
    (plusCartesianInverse J K ⋙ plusCartesianFunctor J K).map f ≫
        ((DerivedCategory.Plus.cohomologyIn
            (cartesianProperty J K.simplicial AddCommGrpCat.{max w u v})).isoMk
          (@asIso _ _ _ _ ((plusDerivedAdjunction J K).counit.app F.obj)
            (plusDerivedCounit_app_isIso_of_cohomologyIn J K F))).hom =
      ((DerivedCategory.Plus.cohomologyIn
          (cartesianProperty J K.simplicial AddCommGrpCat.{max w u v})).isoMk
        (@asIso _ _ _ _ ((plusDerivedAdjunction J K).counit.app E.obj)
          (plusDerivedCounit_app_isIso_of_cohomologyIn J K E))).hom ≫
        (𝟭 (DerivedCategory.Plus.CohomologyIn
            (cartesianProperty J K.simplicial AddCommGrpCat.{max w u v}))).map f :=
  sorry

/-- The counit isomorphism `Ra_* ⋙ a⁻¹ ≅ 𝟭` on `D_A⁺((C / K)_total)`. -/
def plusCartesianCounitIso :
    plusCartesianInverse J K ⋙ plusCartesianFunctor J K ≅
      𝟭 (DerivedCategory.Plus.CohomologyIn
        (cartesianProperty J K.simplicial AddCommGrpCat.{max w u v})) :=
  NatIso.ofComponents
    (fun E ↦
      (DerivedCategory.Plus.cohomologyIn
          (cartesianProperty J K.simplicial AddCommGrpCat.{max w u v})).isoMk
        (@asIso _ _ _ _ ((plusDerivedAdjunction J K).counit.app E.obj)
          (plusDerivedCounit_app_isIso_of_cohomologyIn J K E)))
    (fun f ↦ plusCartesianCounitIso_naturality J K f)

/-- The component of `plusCartesianCounitIso` at `E` is the derived adjunction counit
on the underlying object of `E`. -/
theorem plusCartesianCounitIso_hom_app
    (E : DerivedCategory.Plus.CohomologyIn
      (cartesianProperty J K.simplicial AddCommGrpCat.{max w u v})) :
    ((plusCartesianCounitIso J K).hom.app E).hom =
      (plusDerivedAdjunction J K).counit.app E.obj :=
  sorry

/-- Lemma 85.17.5: Let `C` be a site with equalizers and fibre products. Let `K` be a
hypercovering. Let `A` denote the weak Serre subcategory of cartesian abelian sheaves
on `(C / K)_total`. Then `a⁻¹` defines an equivalence
`D⁺(C) ≌ D_A⁺((C / K)_total)` with quasi-inverse `Ra_*`. -/
@[stacks 0D8I]
def plusCartesianEquivalence :
    DerivedCategory.Plus (Sheaf J AddCommGrpCat.{max w u v}) ≌
      DerivedCategory.Plus.CohomologyIn
        (cartesianProperty J K.simplicial AddCommGrpCat.{max w u v}) :=
  Equivalence.mk (plusCartesianFunctor J K) (plusCartesianInverse J K)
    (plusCartesianUnitIso J K) (plusCartesianCounitIso J K)

/-- The forward functor of `plusCartesianEquivalence` is `a⁻¹` corestricted to
`D_A⁺((C / K)_total)`. -/
theorem plusCartesianEquivalence_functor :
    (plusCartesianEquivalence J K).functor = plusCartesianFunctor J K :=
  sorry

/-- The inverse functor of `plusCartesianEquivalence` is `Ra_*` on
`D_A⁺((C / K)_total)`. -/
theorem plusCartesianEquivalence_inverse :
    (plusCartesianEquivalence J K).inverse = plusCartesianInverse J K :=
  sorry

/-- The corestricted functor `a⁻¹ : D⁺(C) ⥤ D_A⁺((C / K)_total)` is an equivalence. -/
instance plusCartesianFunctor_isEquivalence :
    (plusCartesianFunctor J K).IsEquivalence :=
  Equivalence.isEquivalence_functor (plusCartesianEquivalence J K)

end CategoryTheory.SemiRepresentableFamily
