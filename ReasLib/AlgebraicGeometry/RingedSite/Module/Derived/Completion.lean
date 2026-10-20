/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.Completeness
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.FiniteType
public import ReasLib.CategoryTheory.ObjectProperty.Reflector

@[expose] public section

open CategoryTheory SheafOfModules.RingedSite

noncomputable section
universe u v w

namespace RingedSite.Hom.ModuleDerived.Completion

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
variable {O : Sheaf J CommRingCat.{w}} [UnivLE.{max u v, w}]
variable [∀ X : C, HasWeakSheafify (J.over X) AddCommGrpCat.{w}]
variable [∀ X : C, (J.over X).WEqualsLocallyBijective AddCommGrpCat.{w}]

/-- Finite-type ideal sheaves admit derived completion,
expressed by the universal reflection into derived-complete objects. -/
@[stacks 099F]
instance inclusionIsRightAdjoint (I : Subobject (unitModule J O))
    [(I : ringedSiteModuleCategory J O).IsFiniteType] :
    (derivedCompleteObjectProperty.{u, v, w, w} I).ι.IsRightAdjoint := sorry

/-- A chosen derived-completion reflector, supplied by finite-type reflectivity.
Its universal adjunction determines the choice up to canonical isomorphism. -/
def reflector (I : Subobject (unitModule J O))
    [(I : ringedSiteModuleCategory J O).IsFiniteType] :
    ObjectProperty.Reflector (derivedCompleteObjectProperty.{u, v, w, w} I) :=
  ObjectProperty.Reflector.ofIsRightAdjoint _ (inclusionIsRightAdjoint I)

/-- The derived-completion functor lands in the actual complete full subcategory. -/
def functor (I : Subobject (unitModule J O))
    [(I : ringedSiteModuleCategory J O).IsFiniteType] :=
  (reflector I).toFullSubcategory

/-- The universal completion adjunction for the chosen completion functor. -/
def adjunction (I : Subobject (unitModule J O))
    [(I : ringedSiteModuleCategory J O).IsFiniteType] :
    functor I ⊣ (derivedCompleteObjectProperty.{u, v, w, w} I).ι :=
  (reflector I).adjunction

/-- The canonical map from an ambient object to its derived completion. -/
def unit (I : Subobject (unitModule J O))
    [(I : ringedSiteModuleCategory J O).IsFiniteType] :
    𝟭 _ ⟶ (reflector I).reflection := (adjunction I).unit

/-- Universal completion maps into a complete object are the ambient maps. -/
def homEquiv (I : Subobject (unitModule J O))
    [(I : ringedSiteModuleCategory J O).IsFiniteType]
    (K : RingedSite.Hom.ModuleDerived.{w} (RingedSite.ofCommRingSheaf J O))
    (E : (derivedCompleteObjectProperty.{u, v, w, w} I).FullSubcategory) :
    ((functor I).obj K ⟶ E) ≃ (K ⟶ E.obj) :=
  (adjunction I).homEquiv K E

/-- The completion unit has a complete target and the full universal mapping
property, with the map on morphisms given by precomposition with that unit. -/
theorem unit_spec (I : Subobject (unitModule J O))
    [(I : ringedSiteModuleCategory J O).IsFiniteType]
    (K : RingedSite.Hom.ModuleDerived.{w} (RingedSite.ofCommRingSheaf J O)) :
    IsDerivedCompleteWithRespectTo ((reflector I).reflection.obj K) I ∧
      ∀ E : (derivedCompleteObjectProperty.{u, v, w, w} I).FullSubcategory,
        Function.Bijective (fun g : (functor I).obj K ⟶ E ↦
          (unit I).app K ≫ (derivedCompleteObjectProperty.{u, v, w, w} I).ι.map g) :=
  ⟨((functor I).obj K).property, fun E ↦ ((adjunction I).homEquiv K E).bijective⟩

/-- Every reflector onto this same complete subcategory is canonically
isomorphic to the chosen completion, by uniqueness of left adjoints. -/
def toReflectorIso (I : Subobject (unitModule J O))
    [(I : ringedSiteModuleCategory J O).IsFiniteType]
    (R : ObjectProperty.Reflector (derivedCompleteObjectProperty.{u, v, w, w} I)) :
    functor I ≅ R.toFullSubcategory :=
  (adjunction I).leftAdjointUniq R.adjunction

end RingedSite.Hom.ModuleDerived.Completion
