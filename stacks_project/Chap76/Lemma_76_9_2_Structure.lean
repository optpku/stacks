/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Thickening.Hom

/-!
# Spaces-étale structure sheaves and morphisms of thickenings

The inverse-image structure-sheaf API and lifted-morphism predicate are supplied
by their canonical mathematical owners.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Thickening

#check (AlgebraicGeometry.AlgebraicSpace.Thickening.spacesEtalePushforwardCompIso :
  ∀ {S : Scheme.{u}} {X Y Z : AlgebraicSpace S} (f : X ⟶ Y) (g : Y ⟶ Z),
    (spacesEtalePullback f).sheafPushforwardContinuous (Type u)
        (spacesEtaleTopology Y) (spacesEtaleTopology X) ⋙
      (spacesEtalePullback g).sheafPushforwardContinuous (Type u)
        (spacesEtaleTopology Z) (spacesEtaleTopology Y) ≅
      (spacesEtalePullback (f ≫ g)).sheafPushforwardContinuous (Type u)
        (spacesEtaleTopology Z) (spacesEtaleTopology X))

#check (AlgebraicGeometry.AlgebraicSpace.Thickening.spacesEtalePushforwardCompIso_eq :
  ∀ {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
    (f : X ⟶ Y) (g : Y ⟶ Z),
    spacesEtalePushforwardCompIso f g =
      Functor.sheafPushforwardContinuousComp' (spacesEtalePullbackComp f g).symm (Type u)
        (spacesEtaleTopology Z) (spacesEtaleTopology Y) (spacesEtaleTopology X))

#check (AlgebraicGeometry.AlgebraicSpace.Thickening.inverseImageCompIso :
  ∀ {S : Scheme.{u}} {X Y Z : AlgebraicSpace S} (f : X ⟶ Y) (g : Y ⟶ Z),
    (spacesRingedToposHom (f ≫ g)).toTopos.inverseImage ≅
      (MorphismOfTopoiIn.comp (spacesRingedToposHom g).toTopos
        (spacesRingedToposHom f).toTopos).inverseImage)

#check (AlgebraicGeometry.AlgebraicSpace.Thickening.ringInverseImageCompAssocIso :
  ∀ {S : Scheme.{u}} {X Y Z : AlgebraicSpace S} (f : X ⟶ Y) (g : Y ⟶ Z),
    (spacesRingedToposHom (f ≫ g)).toTopos.ringInverseImage ≅
      (spacesRingedToposHom g).toTopos.ringInverseImage ⋙
        (spacesRingedToposHom f).toTopos.ringInverseImage)

#check (AlgebraicGeometry.AlgebraicSpace.Thickening.ringInverseImageCongr :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} {a b : X ⟶ Y} (h : a = b),
    (spacesRingedToposHom a).toTopos.ringInverseImage ≅
      (spacesRingedToposHom b).toTopos.ringInverseImage)

#check (AlgebraicGeometry.AlgebraicSpace.Thickening.closedStructureSheaf :
  ∀ {S : Scheme.{u}} {X X' : AlgebraicSpace S} (i : X ⟶ X'),
    Sheaf (spacesEtaleTopology X) RingCat.{u})

#check (AlgebraicGeometry.AlgebraicSpace.Thickening.closedStructureSheaf_eq :
  ∀ {S : Scheme.{u}} {X X' : AlgebraicSpace S} (i : X ⟶ X'),
    closedStructureSheaf i =
      (spacesRingedToposHom i).toTopos.ringInverseImage.obj (spacesStructureSheaf X'))

#check (AlgebraicGeometry.AlgebraicSpace.Thickening.closedStructureSheaf_structureMap :
  ∀ {S : Scheme.{u}} {X X' : AlgebraicSpace S} (i : X ⟶ X'),
    closedStructureSheaf i ⟶ spacesStructureSheaf X)

#check (AlgebraicGeometry.AlgebraicSpace.Thickening.closedStructureSheaf_structureMap_eq :
  ∀ {S : Scheme.{u}} {X X' : AlgebraicSpace S} (i : X ⟶ X'),
    closedStructureSheaf_structureMap i = (spacesRingedToposHom i).structureMap)

#check (AlgebraicGeometry.AlgebraicSpace.Thickening.inverseImageClosedStructureSheaf :
  ∀ {S : Scheme.{u}} {X Y Y' : AlgebraicSpace S}
    (f : X ⟶ Y) (iY : Y ⟶ Y'),
    Sheaf (spacesEtaleTopology X) RingCat.{u})

#check (AlgebraicGeometry.AlgebraicSpace.Thickening.inverseImageClosedStructureSheaf_eq :
  ∀ {S : Scheme.{u}} {X Y Y' : AlgebraicSpace S}
    (f : X ⟶ Y) (iY : Y ⟶ Y'),
    inverseImageClosedStructureSheaf f iY =
      (spacesRingedToposHom f).toTopos.ringInverseImage.obj (closedStructureSheaf iY))

#check (AlgebraicGeometry.AlgebraicSpace.Thickening.inverseImageBaseSheaf :
  ∀ {S : Scheme.{u}} {B X : AlgebraicSpace S} (s : X ⟶ B),
    Sheaf (spacesEtaleTopology X) RingCat.{u})

#check (AlgebraicGeometry.AlgebraicSpace.Thickening.inverseImageBaseSheaf_eq :
  ∀ {S : Scheme.{u}} {B X : AlgebraicSpace S} (s : X ⟶ B),
    inverseImageBaseSheaf s =
      (spacesRingedToposHom s).toTopos.ringInverseImage.obj (spacesStructureSheaf B))

#check (AlgebraicGeometry.AlgebraicSpace.Thickening.closedAlgebraMap :
  ∀ {S : Scheme.{u}} {B X X' : AlgebraicSpace S}
    (i : X ⟶ X') (sX : X ⟶ B) (sX' : X' ⟶ B) (hX : i ≫ sX' = sX),
    inverseImageBaseSheaf sX ⟶ closedStructureSheaf i)

#check (AlgebraicGeometry.AlgebraicSpace.Thickening.closedAlgebraMap_eq :
  ∀ {S : Scheme.{u}} {B X X' : AlgebraicSpace S}
    (i : X ⟶ X') (sX : X ⟶ B) (sX' : X' ⟶ B) (hX : i ≫ sX' = sX),
    closedAlgebraMap i sX sX' hX =
      (ringInverseImageCongr hX.symm).hom.app (spacesStructureSheaf B) ≫
        (ringInverseImageCompAssocIso i sX').hom.app (spacesStructureSheaf B) ≫
        (spacesRingedToposHom i).toTopos.ringInverseImage.map
          (spacesRingedToposHom sX').structureMap)

#check (AlgebraicGeometry.AlgebraicSpace.Thickening.inverseImageClosedAlgebraMap :
  ∀ {S : Scheme.{u}} {B X Y Y' : AlgebraicSpace S}
    (sX : X ⟶ B) (sY : Y ⟶ B) (sY' : Y' ⟶ B)
    (f : X ⟶ Y) (iY : Y ⟶ Y') (hY : iY ≫ sY' = sY) (hf : f ≫ sY = sX),
    inverseImageBaseSheaf sX ⟶ inverseImageClosedStructureSheaf f iY)

#check (AlgebraicGeometry.AlgebraicSpace.Thickening.inverseImageClosedAlgebraMap_eq :
  ∀ {S : Scheme.{u}} {B X Y Y' : AlgebraicSpace S}
    (sX : X ⟶ B) (sY : Y ⟶ B) (sY' : Y' ⟶ B)
    (f : X ⟶ Y) (iY : Y ⟶ Y') (hY : iY ≫ sY' = sY) (hf : f ≫ sY = sX),
    inverseImageClosedAlgebraMap sX sY sY' f iY hY hf =
      (ringInverseImageCongr hf.symm).hom.app (spacesStructureSheaf B) ≫
        (ringInverseImageCompAssocIso f sY).hom.app (spacesStructureSheaf B) ≫
        (spacesRingedToposHom f).toTopos.ringInverseImage.map
          (closedAlgebraMap iY sY sY' hY))

#check (AlgebraicGeometry.AlgebraicSpace.Thickening.structureMap_transported :
  ∀ {S : Scheme.{u}} {X X' Y Y' : AlgebraicSpace S}
    (iX : X ⟶ X') (iY : Y ⟶ Y') (f : X ⟶ Y) (f' : X' ⟶ Y')
    (h_comm : iX ≫ f' = f ≫ iY),
    inverseImageClosedStructureSheaf f iY ⟶ closedStructureSheaf iX)

#check (AlgebraicGeometry.AlgebraicSpace.Thickening.structureMap_transported_eq :
  ∀ {S : Scheme.{u}} {X X' Y Y' : AlgebraicSpace S}
    (iX : X ⟶ X') (iY : Y ⟶ Y') (f : X ⟶ Y) (f' : X' ⟶ Y')
    (h_comm : iX ≫ f' = f ≫ iY),
    structureMap_transported iX iY f f' h_comm =
      (ringInverseImageCompAssocIso f iY).inv.app (spacesStructureSheaf Y') ≫
        (ringInverseImageCongr h_comm.symm).hom.app (spacesStructureSheaf Y') ≫
        (ringInverseImageCompAssocIso iX f').hom.app (spacesStructureSheaf Y') ≫
        (spacesRingedToposHom iX).toTopos.ringInverseImage.map
          (spacesRingedToposHom f').structureMap)

#check (AlgebraicGeometry.AlgebraicSpace.Thickening.structureMap_commutes :
  ∀ {S : Scheme.{u}} {X X' Y Y' : AlgebraicSpace S}
    (iX : X ⟶ X') (iY : Y ⟶ Y') (f : X ⟶ Y)
    (α : inverseImageClosedStructureSheaf f iY ⟶ closedStructureSheaf iX),
    Prop)

#check (AlgebraicGeometry.AlgebraicSpace.Thickening.structureMap_commutes_iff :
  ∀ {S : Scheme.{u}} {X X' Y Y' : AlgebraicSpace S}
    (iX : X ⟶ X') (iY : Y ⟶ Y') (f : X ⟶ Y)
    (α : inverseImageClosedStructureSheaf f iY ⟶ closedStructureSheaf iX),
    structureMap_commutes iX iY f α ↔
      α ≫ closedStructureSheaf_structureMap iX =
        (spacesRingedToposHom f).toTopos.ringInverseImage.map
          (closedStructureSheaf_structureMap iY) ≫
        (spacesRingedToposHom f).structureMap)

#check (AlgebraicGeometry.AlgebraicSpace.Thickening.isAlgebraOverBase :
  ∀ {S : Scheme.{u}} {B X X' Y Y' : AlgebraicSpace S}
    (sX : X ⟶ B) (sX' : X' ⟶ B) (sY : Y ⟶ B) (sY' : Y' ⟶ B)
    (iX : X ⟶ X') (iY : Y ⟶ Y') (f : X ⟶ Y)
    (hX : iX ≫ sX' = sX) (hY : iY ≫ sY' = sY) (hf : f ≫ sY = sX)
    (α : inverseImageClosedStructureSheaf f iY ⟶ closedStructureSheaf iX),
    Prop)

#check (AlgebraicGeometry.AlgebraicSpace.Thickening.isAlgebraOverBase_iff :
  ∀ {S : Scheme.{u}} {B X X' Y Y' : AlgebraicSpace S}
    (sX : X ⟶ B) (sX' : X' ⟶ B) (sY : Y ⟶ B) (sY' : Y' ⟶ B)
    (iX : X ⟶ X') (iY : Y ⟶ Y') (f : X ⟶ Y)
    (hX : iX ≫ sX' = sX) (hY : iY ≫ sY' = sY) (hf : f ≫ sY = sX)
    (α : inverseImageClosedStructureSheaf f iY ⟶ closedStructureSheaf iX),
    isAlgebraOverBase sX sX' sY sY' iX iY f hX hY hf α ↔
      inverseImageClosedAlgebraMap sX sY sY' f iY hY hf ≫ α =
        closedAlgebraMap iX sX sX' hX)

#check (AlgebraicGeometry.AlgebraicSpace.Thickening.IsHom :
  ∀ {S : Scheme.{u}} {B X X' Y Y' : AlgebraicSpace S}
    (sX' : X' ⟶ B) (sY' : Y' ⟶ B)
    (iX : X ⟶ X') (iY : Y ⟶ Y') (f : X ⟶ Y)
    (α : inverseImageClosedStructureSheaf f iY ⟶ closedStructureSheaf iX)
    (f' : X' ⟶ Y'),
    Prop)

#check (AlgebraicGeometry.AlgebraicSpace.Thickening.IsHom.of :
  ∀ {S : Scheme.{u}} {B X X' Y Y' : AlgebraicSpace S}
    (sX' : X' ⟶ B) (sY' : Y' ⟶ B)
    (iX : X ⟶ X') (iY : Y ⟶ Y') (f : X ⟶ Y)
    (α : inverseImageClosedStructureSheaf f iY ⟶ closedStructureSheaf iX)
    (f' : X' ⟶ Y') (h_comm : iX ≫ f' = f ≫ iY) (h_over : f' ≫ sY' = sX')
    (hα : structureMap_transported iX iY f f' h_comm = α),
    IsHom sX' sY' iX iY f α f')

#check (AlgebraicGeometry.AlgebraicSpace.Thickening.isHom_iff :
  ∀ {S : Scheme.{u}} {B X X' Y Y' : AlgebraicSpace S}
    (sX' : X' ⟶ B) (sY' : Y' ⟶ B)
    (iX : X ⟶ X') (iY : Y ⟶ Y') (f : X ⟶ Y)
    (α : inverseImageClosedStructureSheaf f iY ⟶ closedStructureSheaf iX)
    (f' : X' ⟶ Y'),
    IsHom sX' sY' iX iY f α f' ↔
      ∃ h_comm : iX ≫ f' = f ≫ iY,
        f' ≫ sY' = sX' ∧ structureMap_transported iX iY f f' h_comm = α)

end AlgebraicGeometry.AlgebraicSpace.Thickening
