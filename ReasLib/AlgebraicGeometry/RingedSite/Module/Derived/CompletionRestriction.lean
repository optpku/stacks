module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Ideal.Extension
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.FiniteType
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Flat
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Ideal.Quotient
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.Completeness
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.Coextension
public import ReasLib.CategoryTheory.ObjectProperty.FullSubcategory.Restriction

/-!
# Derived-completeness restriction

This module records the transport of derived completeness under restriction of
scalars for morphisms of commutative ring sheaves on a fixed site.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open SheafOfModules.RingedSite
open SheafOfModules.RingedSite.DerivedCoextension

noncomputable section

universe u

namespace RingedSite.Hom.ModuleDerived

variable {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
variable [HasWeakSheafify J AddCommGrpCat.{u}]
variable [HasSheafify J AddCommGrpCat.{u}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable {O O' : Sheaf J CommRingCat.{u}}

/-- Restriction of scalars identifies derived-complete objects for an ideal sheaf with
derived-complete objects for its extension along the ring-sheaf morphism. -/
theorem derivedCompleteObjectProperty_inverseImage
    (alpha : O ⟶ O') (I : Subobject (unitModule J O)) :
    (derivedCompleteObjectProperty I).inverseImage
        (restriction alpha) =
      derivedCompleteObjectProperty (IdealSheaf.extension I alpha) := sorry

/-- Restriction of scalars on derived-complete full subcategories for an ideal sheaf
and its extension along a ring-sheaf morphism. -/
abbrev derivedCompleteRestriction
    (alpha : O ⟶ O') (I : Subobject (unitModule J O)) :
    (derivedCompleteObjectProperty (IdealSheaf.extension I alpha)).FullSubcategory ⥤
      (derivedCompleteObjectProperty I).FullSubcategory :=
  ObjectProperty.FullSubcategory.restrict
    (DerivedCoextension.restriction alpha)
    (le_of_eq (derivedCompleteObjectProperty_inverseImage alpha I).symm)

/-- The underlying object of the restricted functor is derived restriction of the
underlying derived module. -/
theorem derivedCompleteRestriction_obj
    (alpha : O ⟶ O') (I : Subobject (unitModule J O))
    (K : (derivedCompleteObjectProperty
      (IdealSheaf.extension I alpha)).FullSubcategory) :
    ((derivedCompleteRestriction alpha I).obj K).obj =
      (DerivedCoextension.restriction alpha).obj K.obj := sorry

/-- Under flatness and the quotient comparison for a finite-type ideal sheaf,
restriction induces an equivalence on the derived-complete categories. -/
theorem derivedCompleteRestrictionIsEquivalence
    (alpha : O ⟶ O') (I : Subobject (unitModule J O))
    [(I : ringedSiteModuleCategory J O).IsFiniteType]
    [IsFlat O ((restrictionAlong alpha).obj (unitModule J O'))]
    [IsIso (IdealSheaf.TargetQuotient.ringMap alpha I)] :
    (derivedCompleteRestriction alpha I).IsEquivalence := sorry

end RingedSite.Hom.ModuleDerived
