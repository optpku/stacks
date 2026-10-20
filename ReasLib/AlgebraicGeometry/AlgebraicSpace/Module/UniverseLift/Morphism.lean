/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.UniverseLift

/-! # Universe lifting of module morphisms

Module morphisms lift sectionwise, and the lifted structure module has a concrete
comparison with the structure module of the lifted ringed site.
-/

@[expose] public section

open CategoryTheory CategoryTheory.MonoidalCategory
open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace.Modules
open SheafOfModules.RingedSite

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

namespace Modules

/-- A morphism of commutative `𝒪_X`-modules lifts on sections over `U` by universe-lifting
the component at `U`. -/
noncomputable def liftedSectionMap {S : Scheme.{u}} {X : AlgebraicSpace S}
    {F G : commModules X} (f : F ⟶ G) (U : (smallEtaleSite X)ᵒᵖ) :
    liftedSection F U ⟶ liftedSection G U :=
  eqToHom (liftedSection_eq F U).symm ≫
    (ModuleCat.restrictScalars (ULift.ringEquiv.{u, u + 1}).toRingHom).map
      ((ModuleCat.uliftFunctor.{u + 1, u} ((commStructureSheaf X).obj.obj U)).map
        (f.val.app U)) ≫
    eqToHom (liftedSection_eq G U)

/-- `liftedSectionMap` is restriction of scalars of the universe lift of the component
at `U`. -/
theorem liftedSectionMap_eq {S : Scheme.{u}} {X : AlgebraicSpace S}
    {F G : commModules X} (f : F ⟶ G) (U : (smallEtaleSite X)ᵒᵖ) :
    liftedSectionMap f U =
      eqToHom (liftedSection_eq F U).symm ≫
        (ModuleCat.restrictScalars (ULift.ringEquiv.{u, u + 1}).toRingHom).map
          ((ModuleCat.uliftFunctor.{u + 1, u} ((commStructureSheaf X).obj.obj U)).map
            (f.val.app U)) ≫
        eqToHom (liftedSection_eq G U) :=
  rfl

/-- A morphism of commutative `𝒪_X`-modules lifts to the universe-lifted presentation by
applying `ULift` sectionwise. -/
noncomputable def liftCommModuleMap {S : Scheme.{u}} {X : AlgebraicSpace S}
    {F G : commModules X} (f : F ⟶ G) :
    liftCommModule F ⟶ liftCommModule G where
  val :=
    { app := fun U ↦ liftedSectionMap f U
      naturality := sorry }

/-- The underlying natural transformation of `liftCommModuleMap` is `liftedSectionMap`. -/
theorem liftCommModuleMap_val_app {S : Scheme.{u}} {X : AlgebraicSpace S}
    {F G : commModules X} (f : F ⟶ G) (U : (smallEtaleSite X)ᵒᵖ) :
    (liftCommModuleMap f).val.app U = liftedSectionMap f U :=
  rfl

/-- A morphism of `𝒪_X`-modules lifts to the universe-lifted commutative presentation. -/
noncomputable def liftModuleMap {S : Scheme.{u}} {X : AlgebraicSpace S}
    {F G : X.Modules} (f : F ⟶ G) :
    liftModule F ⟶ liftModule G :=
  liftCommModuleMap ((toCommModules X).map f)

/-- `liftModuleMap` is `liftCommModuleMap` of the commutative presentation of `f`. -/
theorem liftModuleMap_eq {S : Scheme.{u}} {X : AlgebraicSpace S}
    {F G : X.Modules} (f : F ⟶ G) :
    liftModuleMap f = liftCommModuleMap ((toCommModules X).map f) :=
  rfl

/-- The universe lift of the structure module is the tensor unit of the lifted commutative
presentation, on sections. -/
noncomputable def liftedUnitIso {S : Scheme.{u}} (X : AlgebraicSpace S) :
    liftModule (SheafOfModules.unit (structureSheaf X)) ≅
      unitModule (smallEtaleTopology X) (commStructureSheafLift X) where
  hom :=
    { val :=
        { app := fun U ↦ 𝟙 _
          naturality := sorry } }
  inv :=
    { val :=
        { app := fun U ↦ 𝟙 _
          naturality := sorry } }
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- The forward map of `liftedUnitIso` is the identity on sections. -/
theorem liftedUnitIso_hom_app {S : Scheme.{u}} (X : AlgebraicSpace S)
    (U : (smallEtaleSite X)ᵒᵖ) :
    (liftedUnitIso X).hom.val.app U = 𝟙 _ :=
  rfl

end Modules

end AlgebraicGeometry.AlgebraicSpace
