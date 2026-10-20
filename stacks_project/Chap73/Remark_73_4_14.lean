/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.RingedSite.BigRelocalization

/-!
# Remark 73.4.14

The big and spaces-étale structure sheaves admit the canonical ringed upgrades
of relocalization, projection, and the morphisms induced by algebraic-space maps.
-/

@[expose] public section

open CategoryTheory Opposite AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Etale

noncomputable section

universe u

variable {S : Scheme.{u}} {X Y Z : AlgebraicSpace S} (f : Y ⟶ X) (g : Z ⟶ Y)

/- Remark 73.4.14: relocalization carries its canonical invertible inverse-image
structure map, making it a morphism of ringed topoi. -/
@[stacks 0DF9] #check
  (AlgebraicGeometry.AlgebraicSpace.Etale.SpacesToBig.relocalizationRingedHom :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S},
      (Y ⟶ X) → RingedSite.ToposHom (spacesRingedSite Y) (Big.ringedSite X))

#check (AlgebraicGeometry.AlgebraicSpace.spacesStructureSheaf :
  ∀ {S : Scheme.{u}} (X : AlgebraicSpace S),
    Sheaf (spacesEtaleTopology X) RingCat.{u})

#check (AlgebraicGeometry.AlgebraicSpace.Etale.Big.structureSheaf :
  ∀ {S : Scheme.{u}} (X : AlgebraicSpace S),
    Sheaf (overEtaleTopology X) RingCat.{u})

#check (AlgebraicGeometry.AlgebraicSpace.Etale.Big.structureSheaf_obj :
  ∀ {S : Scheme.{u}} (X : AlgebraicSpace S) (U : Over X),
    (Big.structureSheaf X).obj.obj (op U) = Big.gamma U.left)

#check (AlgebraicGeometry.AlgebraicSpace.Etale.Big.structureSheaf_map :
  ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} {U V : Over X} (h : U ⟶ V),
    (Big.structureSheaf X).obj.map h.op = Big.gammaMap h.left)

#check (AlgebraicGeometry.AlgebraicSpace.Etale.Big.gamma_eq :
  ∀ {S : Scheme.{u}} (U : AlgebraicSpace S),
    Big.gamma U = (spacesStructureSheaf U).obj.obj (op (spacesEtaleSite.self U)))

#check (AlgebraicGeometry.AlgebraicSpace.Etale.SpacesToBig.relocalizationStructureSheafMap f :
  spacesStructureSheaf Y ⟶
    (SpacesToBig.relocalizationPushforward f).obj (Big.structureSheaf X))

#check (AlgebraicGeometry.AlgebraicSpace.Etale.SpacesToBig.relocalizationStructureSheafMap_app f :
  ∀ U : spacesEtaleSite Y,
    (SpacesToBig.relocalizationStructureSheafMap f).hom.app (op U) =
      Big.spacesStructureToGamma U)

#check (AlgebraicGeometry.AlgebraicSpace.Etale.SpacesToBig.relocalizationRingedHom_structureMap f :
  (SpacesToBig.relocalizationRingedHom f).structureMap = SpacesToBig.relocalizationSharp f)

#check (AlgebraicGeometry.AlgebraicSpace.Etale.SpacesToBig.relocalizationMorphismOfTopoi_inverseImage f :
  (SpacesToBig.relocalizationMorphismOfTopoi f).inverseImage =
    (SpacesToBig.relocalizationFunctor f).sheafPushforwardContinuous (Type u)
      (spacesEtaleTopology Y) (overEtaleTopology X))

#check (AlgebraicGeometry.AlgebraicSpace.Etale.SpacesToBig.relocalizationSharp_underlying f :
  (sheafCompose (spacesEtaleTopology Y) (forget RingCat.{u})).map
    (SpacesToBig.relocalizationSharp f) = SpacesToBig.relocalizationSharpUnderlying f)

#check (AlgebraicGeometry.AlgebraicSpace.Etale.SpacesToBig.relocalizationSharp_isIso f :
  IsIso (SpacesToBig.relocalizationSharp f))

#check (AlgebraicGeometry.AlgebraicSpace.Etale.SpacesToBig.identityRingedRelocalization X :
  RingedSite.ToposHom (spacesRingedSite X) (Big.ringedSite X))

#check (AlgebraicGeometry.AlgebraicSpace.Etale.SpacesToBig.identityRingedRelocalization_eq X :
  SpacesToBig.identityRingedRelocalization X = SpacesToBig.relocalizationRingedHom (𝟙 X))

#check (AlgebraicGeometry.AlgebraicSpace.Etale.SpacesToBig.siteHom X :
  RingedSite.Hom (Big.ringedSite X) (spacesRingedSite X))

#check (AlgebraicGeometry.AlgebraicSpace.Etale.SpacesToBig.siteSharp_app X :
  ∀ U : spacesEtaleSite X,
    (SpacesToBig.siteSharp X).hom.app (op U) = Big.spacesStructureToGamma U)

#check (AlgebraicGeometry.AlgebraicSpace.ringedToposHom :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S},
    (X ⟶ Y) → RingedSite.ToposHom
      (AlgebraicGeometry.AlgebraicSpace.ringedSite X)
      (AlgebraicGeometry.AlgebraicSpace.ringedSite Y))

#check (AlgebraicGeometry.AlgebraicSpace.spacesRingedToposHom :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S},
    (X ⟶ Y) → RingedSite.ToposHom (spacesRingedSite X) (spacesRingedSite Y))

#check (AlgebraicGeometry.AlgebraicSpace.Etale.Big.ringedHom f :
  RingedSite.ToposHom (Big.ringedSite Y) (Big.ringedSite X))

#check (AlgebraicGeometry.AlgebraicSpace.Etale.Big.sharp_app f :
  ∀ U : Over Y, (Big.sharp f).hom.app (op U) = 𝟙 (Big.gamma U.left))

#check (AlgebraicGeometry.AlgebraicSpace.Etale.Big.ringedHom_structureMap_isIso f :
  IsIso (Big.ringedHom f).structureMap)

#check (AlgebraicGeometry.AlgebraicSpace.Etale.Big.ringedHomCompIso f g :
  RingedSite.ToposHom.TwoIso.{u + 1, u + 1, u + 1, u + 1, u}
    (RingedSite.ToposHom.comp.{u + 1, u + 1, u + 1, u + 1, u + 1, u + 1, u}
      (Big.ringedHom g) (Big.ringedHom f)) (Big.ringedHom (g ≫ f)))

#check (AlgebraicGeometry.AlgebraicSpace.Etale.Big.ringedHomIdIso X :
  RingedSite.ToposHom.TwoIso.{u + 1, u + 1, u + 1, u + 1, u} (Big.ringedHom (𝟙 X))
    (RingedSite.ToposHom.id (Big.ringedSite X)))

#check (AlgebraicGeometry.AlgebraicSpace.Etale.SpacesToBig.relocalizationRingedHomCompIso f g :
  RingedSite.ToposHom.TwoIso.{u + 1, u + 1, u + 1, u + 1, u}
    (RingedSite.ToposHom.comp.{u + 1, u + 1, u + 1, u + 1, u + 1, u + 1, u}
      (SpacesToBig.relocalizationRingedHom g) (Big.ringedHom f))
    (SpacesToBig.relocalizationRingedHom (g ≫ f)))
