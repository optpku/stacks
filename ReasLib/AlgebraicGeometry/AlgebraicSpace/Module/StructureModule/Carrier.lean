/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.StructureModule
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.RingedSite.CommRingHom

/-! # Underlying structure-module carrier comparisons -/

@[expose] public section

open CategoryTheory CategoryTheory.MonoidalCategory
open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules

variable {S : Scheme.{u}} {X : AlgebraicSpace S}

/-- The forgetful type sheaf of `commStructureSheaf Y` maps to the type-valued
sheaf underlying the structure module of `Y`. -/
noncomputable def forgetToStructureUnitCarrier (Y : AlgebraicSpace S) :
    (sheafCompose (smallEtaleTopology Y) (forget RingCat.{u})).obj
        ((sheafCompose (smallEtaleTopology Y)
            (forget₂ CommRingCat.{u} RingCat.{u})).obj (commStructureSheaf Y)) ⟶
      (Sheaf.InternalModule.ToInternal.underlying (structureSheaf Y)).obj
        (SheafOfModules.unit (structureSheaf Y)) :=
  InducedCategory.homMk
    { app := fun U ↦ 𝟙 _
      naturality := fun {_ _} _ ↦ sorry }

/-- The type-valued sheaf underlying the structure module of `Y` maps to the
forgetful type sheaf of `commStructureSheaf Y`. -/
noncomputable def structureUnitCarrierToForget (Y : AlgebraicSpace S) :
    (Sheaf.InternalModule.ToInternal.underlying (structureSheaf Y)).obj
        (SheafOfModules.unit (structureSheaf Y)) ⟶
      (sheafCompose (smallEtaleTopology Y) (forget RingCat.{u})).obj
        ((sheafCompose (smallEtaleTopology Y)
            (forget₂ CommRingCat.{u} RingCat.{u})).obj (commStructureSheaf Y)) :=
  InducedCategory.homMk
    { app := fun U ↦ 𝟙 _
      naturality := fun {_ _} _ ↦ sorry }

/-- `structureUnitCarrierToForget` is inverse to `forgetToStructureUnitCarrier`
on underlying type sheaves. -/
theorem structureUnitCarrierToForget_comp (Y : AlgebraicSpace S) :
    forgetToStructureUnitCarrier Y ≫ structureUnitCarrierToForget Y = 𝟙 _ :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Modules
