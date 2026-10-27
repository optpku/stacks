/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Sites.Hypercovering.PresheafTarget.DerivedDescent
public import ReasLib.CategoryTheory.DerivedCategory.CohomologyIn.Bounded
public import ReasLib.CategoryTheory.ObjectProperty.WeakSerre

/-!
# Bounded-below cartesian derived descent for terminal hypercoverings
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
      (cartesianProperty J K.simplicial AddCommGrpCat.{max w u v}) := sorry

/-- Derived inverse image `a⁻¹` sends every object of `D⁺(C)` to an object of
`D⁺((C / K)_total)` whose cohomology sheaves are cartesian. -/
theorem plusInverseImageDerived_cohomologyIn
    (E : DerivedCategory.Plus (Sheaf J AddCommGrpCat.{max w u v})) :
    DerivedCategory.Plus.cohomologyIn
      (cartesianProperty J K.simplicial AddCommGrpCat.{max w u v})
      ((plusInverseImageDerived J K).obj E) := sorry

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
      plusInverseImageDerived J K := sorry

/-- The derived adjunction counit is an isomorphism on objects of
`D_A⁺((C / K)_total)`. -/
instance plusDerivedCounit_app_isIso_of_cohomologyIn
    (E : DerivedCategory.Plus.CohomologyIn
      (cartesianProperty J K.simplicial AddCommGrpCat.{max w u v})) :
    IsIso ((plusDerivedAdjunction J K).counit.app E.obj) := sorry

/-- The unit isomorphism `𝟭 ≅ a⁻¹ ⋙ Ra_*` on `D⁺(C)`. -/
def plusCartesianUnitIso :
    𝟭 (DerivedCategory.Plus (Sheaf J AddCommGrpCat.{max w u v})) ≅
      plusCartesianFunctor J K ⋙ plusCartesianInverse J K :=
  NatIso.ofComponents
    (fun (E : DerivedCategory.Plus (Sheaf J AddCommGrpCat.{max w u v})) ↦
      let component := asIso ((plusDerivedUnit J K).app E)
      component)
    (fun f ↦ (plusDerivedUnit J K).naturality f)

/-- The component of `plusCartesianUnitIso` at `E` is the derived adjunction unit. -/
theorem plusCartesianUnitIso_hom_app
    (E : DerivedCategory.Plus (Sheaf J AddCommGrpCat.{max w u v})) :
    (plusCartesianUnitIso J K).hom.app E = (plusDerivedUnit J K).app E := sorry

/-- The counit isomorphism `Ra_* ⋙ a⁻¹ ≅ 𝟭` on `D_A⁺((C / K)_total)`. -/
def plusCartesianCounitIso :
    plusCartesianInverse J K ⋙ plusCartesianFunctor J K ≅
      𝟭 (DerivedCategory.Plus.CohomologyIn
        (cartesianProperty J K.simplicial AddCommGrpCat.{max w u v})) :=
  NatIso.ofComponents
    (fun (E : DerivedCategory.Plus.CohomologyIn
        (cartesianProperty J K.simplicial AddCommGrpCat.{max w u v})) ↦
      let component := asIso ((plusDerivedAdjunction J K).counit.app E.obj)
      (DerivedCategory.Plus.cohomologyIn
        (cartesianProperty J K.simplicial AddCommGrpCat.{max w u v})).isoMk component)
    (fun f ↦ ObjectProperty.hom_ext
      (DerivedCategory.Plus.cohomologyIn
        (cartesianProperty J K.simplicial AddCommGrpCat.{max w u v}))
      ((plusDerivedAdjunction J K).counit.naturality f.hom))

/-- The component of `plusCartesianCounitIso` at `E` is the derived adjunction counit
on the underlying object of `E`. -/
theorem plusCartesianCounitIso_hom_app
    (E : DerivedCategory.Plus.CohomologyIn
      (cartesianProperty J K.simplicial AddCommGrpCat.{max w u v})) :
    ((plusCartesianCounitIso J K).hom.app E).hom =
      (plusDerivedAdjunction J K).counit.app E.obj := sorry

/-- Derived inverse image along a terminal hypercovering gives an equivalence between
bounded-below derived abelian sheaves and total-site objects with cartesian cohomology,
with quasi-inverse the derived direct image. -/
def plusCartesianEquivalence :
    DerivedCategory.Plus (Sheaf J AddCommGrpCat.{max w u v}) ≌
      DerivedCategory.Plus.CohomologyIn
        (cartesianProperty J K.simplicial AddCommGrpCat.{max w u v}) :=
  Equivalence.mk (plusCartesianFunctor J K) (plusCartesianInverse J K)
    (plusCartesianUnitIso J K) (plusCartesianCounitIso J K)

/-- The forward functor of `plusCartesianEquivalence` is `a⁻¹` corestricted to
`D_A⁺((C / K)_total)`. -/
theorem plusCartesianEquivalence_functor :
    (plusCartesianEquivalence J K).functor = plusCartesianFunctor J K := sorry

/-- The inverse functor of `plusCartesianEquivalence` is `Ra_*` on
`D_A⁺((C / K)_total)`. -/
theorem plusCartesianEquivalence_inverse :
    (plusCartesianEquivalence J K).inverse = plusCartesianInverse J K := sorry

/-- The corestricted functor `a⁻¹ : D⁺(C) ⥤ D_A⁺((C / K)_total)` is an equivalence. -/
instance plusCartesianFunctor_isEquivalence :
    (plusCartesianFunctor J K).IsEquivalence :=
  Equivalence.isEquivalence_functor (plusCartesianEquivalence J K)

end CategoryTheory.SemiRepresentableFamily
