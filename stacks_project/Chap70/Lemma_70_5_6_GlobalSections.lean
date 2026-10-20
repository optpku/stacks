module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.GlobalSections

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules

variable {S : Scheme.{u}}

/-- Successive module pullbacks identify with pullback along the composite morphism. -/
abbrev pullbackComp {X Y Z : AlgebraicSpace S} (f : X ⟶ Y) (g : Y ⟶ Z) :
    pullback g ⋙ pullback f ≅ pullback (f ≫ g) :=
  pullbackCompIso f g

#check (globalSections : ∀ {X : AlgebraicSpace S} (F : X.Modules),
    AddCommGrpCat.{u + 1})

#check (globalSections_obj : ∀ {X : AlgebraicSpace S} (F : X.Modules),
    globalSections F = AddCommGrpCat.of (SheafOfModules.unit (structureSheaf X) ⟶ F))

#check (globalSectionsMap : ∀ {X : AlgebraicSpace S} {F G : X.Modules} (φ : F ⟶ G),
    globalSections F ⟶ globalSections G)

#check (globalSectionsMap_eq : ∀ {X : AlgebraicSpace S} {F G : X.Modules} (φ : F ⟶ G)
    (ψ : SheafOfModules.unit (structureSheaf X) ⟶ F),
    (globalSectionsMap φ).hom ψ = ψ ≫ φ)

#check (unitCarrierIso : ∀ (X : AlgebraicSpace S),
    (Sheaf.InternalModule.ToInternal.underlying (structureSheaf X)).obj
      (SheafOfModules.unit (structureSheaf X)) ≅
      (sheafCompose (smallEtaleTopology X) (forget RingCat.{u})).obj (structureSheaf X))

#check (inverseImageUnitCarrierIso : ∀ {X Y : AlgebraicSpace S} (f : X ⟶ Y),
    (Sheaf.InternalModule.ToInternal.underlying
          ((ringedToposHom f).toTopos.ringInverseImage.obj (structureSheaf Y))).obj
      (SheafOfModules.unit
        ((ringedToposHom f).toTopos.ringInverseImage.obj (structureSheaf Y))) ≅
      (sheafCompose (smallEtaleTopology X) (forget RingCat.{u})).obj
        ((ringedToposHom f).toTopos.ringInverseImage.obj (structureSheaf Y)))

#check (moduleInverseImageUnitIso : ∀ {X Y : AlgebraicSpace S} (f : X ⟶ Y),
    ((ringedToposHom f).toTopos.moduleInverseImage (structureSheaf Y)).obj
        (SheafOfModules.unit (structureSheaf Y)) ≅
      SheafOfModules.unit
        ((ringedToposHom f).toTopos.ringInverseImage.obj (structureSheaf Y)))

#check (extendScalarsUnitFromStructure : ∀ {X Y : AlgebraicSpace S} (f : X ⟶ Y),
    SheafOfModules.unit (structureSheaf X) ⟶
      (SheafOfModules.ChangeOfRings.extendScalars (ringedToposHom f).structureMap).obj
        (SheafOfModules.unit
          ((ringedToposHom f).toTopos.ringInverseImage.obj (structureSheaf Y))))

#check (structureModulePullbackInv : ∀ {X Y : AlgebraicSpace S} (f : X ⟶ Y),
    SheafOfModules.unit (structureSheaf X) ⟶
      (pullback f).obj (SheafOfModules.unit (structureSheaf Y)))

#check (structureModulePullbackIso : ∀ {X Y : AlgebraicSpace S} (f : X ⟶ Y),
    SheafOfModules.unit (structureSheaf X) ≅
      (pullback f).obj (SheafOfModules.unit (structureSheaf Y)))

#check (globalSectionsPullback : ∀ {X Y : AlgebraicSpace S} (f : X ⟶ Y) (F : Y.Modules),
    globalSections F ⟶ globalSections ((pullback f).obj F))

#check (globalSectionsPullbackComp : ∀ {X Y Z : AlgebraicSpace S} (f : X ⟶ Y) (g : Y ⟶ Z)
    (F : Z.Modules),
    globalSections ((pullback g).obj F) ⟶
      globalSections ((pullback (f ≫ g)).obj F))

#check (globalSectionsPullback_comp : ∀ {X Y Z : AlgebraicSpace S} (f : X ⟶ Y) (g : Y ⟶ Z)
    (F : Z.Modules),
    globalSectionsPullback g F ≫ globalSectionsPullbackComp f g F =
      globalSectionsPullback (f ≫ g) F)

end AlgebraicGeometry.AlgebraicSpace.Modules
