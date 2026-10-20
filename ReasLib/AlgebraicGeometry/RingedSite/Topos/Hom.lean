/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.Topos.StructureSheaf
public import ReasLib.CategoryTheory.Sites.Topos.InternalRing
import Mathlib.Tactic.CrossRefAttribute

/-!
# Arbitrary morphisms of ringed topoi

A morphism between site-presented ringed topoi consists of an underlying morphism of topoi and
a morphism from the canonical ring-valued inverse image of the target structure sheaf to the
source structure sheaf.  Direct-image presentations are converted through the canonical
internal-ring adjunction, so auxiliary choices of a ring-valued direct image are not retained in
the core structure.
-/

@[expose] public section

open CategoryTheory
open scoped MorphismOfTopoiIn

noncomputable section

universe uX vX uY vY uZ vZ w

namespace RingedSite

/-- A morphism between site-presented ringed topoi, in the canonical inverse-image form
`f⁻¹𝒪_Y ⟶ 𝒪_X`. -/
@[stacks 01D3 "(2), arbitrary"]
structure ToposHom
    (X : RingedSite.{uX, vX, w}) (Y : RingedSite.{uY, vY, w})
    [X.siteTopology.HasSheafCompose (forget RingCat.{w})]
    [Y.siteTopology.HasSheafCompose (forget RingCat.{w})] where
  /-- The underlying morphism of topoi. -/
  toTopos : MorphismOfTopoiIn.{uY, uX, vY, vX, w}
    Y.siteTopology X.siteTopology
  /-- The inverse-image-form structure-sheaf map `f⁻¹𝒪_Y ⟶ 𝒪_X`. -/
  structureMap :
    toTopos.ringInverseImage.obj Y.structureSheaf ⟶ X.structureSheaf

namespace ToposHom

variable {X : RingedSite.{uX, vX, w}} {Y : RingedSite.{uY, vY, w}}
  {Z : RingedSite.{uZ, vZ, w}}
variable [X.siteTopology.HasSheafCompose (forget RingCat.{w})]
  [Y.siteTopology.HasSheafCompose (forget RingCat.{w})]
  [Z.siteTopology.HasSheafCompose (forget RingCat.{w})]

namespace Direct

open CategoryTheory.Sheaf.InternalRing

variable (toTopos : MorphismOfTopoiIn.{uY, uX, vY, vX, w}
  Y.siteTopology X.siteTopology)
variable (ringPushforward :
  Sheaf X.siteTopology RingCat.{w} ⥤ Sheaf Y.siteTopology RingCat.{w})
variable (forgetIso :
  ringPushforward ⋙ sheafCompose Y.siteTopology (forget RingCat.{w}) ≅
    sheafCompose X.siteTopology (forget RingCat.{w}) ⋙ toTopos.pushforward)
variable (structureMap : Y.structureSheaf ⟶ ringPushforward.obj X.structureSheaf)

/-- The underlying type-valued direct-image map supplied by a direct-image presentation. -/
abbrev underlyingMap : Hom.underlyingStructureSheaf Y ⟶
    toTopos.pushforward.obj (Hom.underlyingStructureSheaf X) :=
  (sheafCompose Y.siteTopology (forget RingCat.{w})).map structureMap ≫
    forgetIso.hom.app X.structureSheaf

/-- A direct-image presentation is ring-compatible when its underlying structure map preserves
the canonical internal-ring operations on direct image. -/
abbrev IsRingCompatible : Prop :=
  @IsRingHom (Sheaf Y.siteTopology (Type w)) _ _
    (RingObjects.carrier Y.siteTopology (toInternal.obj Y.structureSheaf))
    (RingObjects.carrier Y.siteTopology
      (toTopos.internalRingDirectImage.obj (toInternal.obj X.structureSheaf)))
    (RingObjects.ringObj Y.siteTopology
      (toInternal.obj Y.structureSheaf)).toAddGrpObj.toAddMonObj
    (RingObjects.ringObj Y.siteTopology
      (toTopos.internalRingDirectImage.obj
        (toInternal.obj X.structureSheaf))).toAddGrpObj.toAddMonObj
    (RingObjects.ringObj Y.siteTopology (toInternal.obj Y.structureSheaf)).toMonObj
    (RingObjects.ringObj Y.siteTopology
      (toTopos.internalRingDirectImage.obj (toInternal.obj X.structureSheaf))).toMonObj
    (underlyingMap toTopos ringPushforward forgetIso structureMap)

/-- The internal-ring direct-image morphism associated to a compatible direct presentation. -/
noncomputable def internalMap
    (h : IsRingCompatible toTopos ringPushforward forgetIso structureMap) :
    RingObjects.Hom Y.siteTopology (toInternal.obj Y.structureSheaf)
      (toTopos.internalRingDirectImage.obj (toInternal.obj X.structureSheaf)) :=
  @RingObjCat.Hom.mk (Sheaf Y.siteTopology (Type w)) _ _
    (sheafBraidedCategory Y.siteTopology) _ _
    (underlyingMap toTopos ringPushforward forgetIso structureMap) h

/-- The internal-ring inverse-image mate of a compatible direct presentation. -/
noncomputable def inverseMap
    (h : IsRingCompatible toTopos ringPushforward forgetIso structureMap) :
    RingObjects.Hom X.siteTopology
      (toTopos.internalRingInverseImage.obj (toInternal.obj Y.structureSheaf))
      (toInternal.obj X.structureSheaf) :=
  (toTopos.internalRingAdjunction.homEquiv _ _).symm
    (internalMap toTopos ringPushforward forgetIso structureMap h)

/-- The canonical ring-valued inverse-image structure map reconstructed from a compatible
direct presentation. -/
noncomputable def inverseStructureMap
    (h : IsRingCompatible toTopos ringPushforward forgetIso structureMap) :
    toTopos.ringInverseImage.obj Y.structureSheaf ⟶ X.structureSheaf :=
  fromInternal.map (inverseMap toTopos ringPushforward forgetIso structureMap h) ≫
    toFromIso.hom.app X.structureSheaf

end Direct

/-- Construct a ringed-topos morphism from a compatible direct-image presentation.  The
auxiliary direct-image functor is used only to form the canonical inverse-image mate. -/
noncomputable def ofDirectImage
    (toTopos : MorphismOfTopoiIn.{uY, uX, vY, vX, w}
      Y.siteTopology X.siteTopology)
    (ringPushforward :
      Sheaf X.siteTopology RingCat.{w} ⥤ Sheaf Y.siteTopology RingCat.{w})
    (forgetIso :
      ringPushforward ⋙ sheafCompose Y.siteTopology (forget RingCat.{w}) ≅
        sheafCompose X.siteTopology (forget RingCat.{w}) ⋙ toTopos.pushforward)
    (structureMap : Y.structureSheaf ⟶ ringPushforward.obj X.structureSheaf)
    (h : Direct.IsRingCompatible toTopos ringPushforward forgetIso structureMap) :
    ToposHom X Y where
  toTopos := toTopos
  structureMap := Direct.inverseStructureMap
    toTopos ringPushforward forgetIso structureMap h

/-- The identity morphism of a site-presented ringed topos. -/
noncomputable def id (X : RingedSite.{uX, vX, w})
    [X.siteTopology.HasSheafCompose (forget RingCat.{w})] : ToposHom X X where
  toTopos := MorphismOfTopoiIn.id X.siteTopology
  structureMap :=
    (MorphismOfTopoiIn.ringInverseImageIdIso
      (J₀ := X.siteTopology)).hom.app X.structureSheaf

/-- The inverse-image structure-sheaf map after forgetting to type-valued sheaves. -/
noncomputable abbrev underlyingMap (f : ToposHom X Y) :
    f.toTopos.inverseImage.obj (Hom.underlyingStructureSheaf Y) ⟶
      Hom.underlyingStructureSheaf X :=
  f.toTopos.ringInverseImageForgetIso.inv.app Y.structureSheaf ≫
    (sheafCompose X.siteTopology (forget RingCat.{w})).map f.structureMap

/-- The direct-image form of the structure-sheaf map, obtained from the canonical ring-valued
adjunction. -/
noncomputable def directStructureMap (f : ToposHom X Y) :
    Y.structureSheaf ⟶ f.toTopos.ringDirectImage.obj X.structureSheaf :=
  (f.toTopos.ringAdjunction.homEquiv _ _) f.structureMap

/-- The direct-image structure-sheaf map after forgetting to type-valued sheaves. -/
noncomputable abbrev underlyingDirectImageMap (f : ToposHom X Y) :
    Hom.underlyingStructureSheaf Y ⟶
      f.toTopos.pushforward.obj (Hom.underlyingStructureSheaf X) :=
  (sheafCompose Y.siteTopology (forget RingCat.{w})).map f.directStructureMap ≫
    f.toTopos.ringDirectImageForgetIso.hom.app X.structureSheaf

/-- Forgetting the ring-valued direct structure map agrees with taking the adjunct of the
underlying inverse-image map. -/
theorem underlyingDirectImageMap_eq_adjunct (f : ToposHom X Y) :
    f.underlyingDirectImageMap =
      (f.toTopos.adjunction.homEquiv _ _) f.underlyingMap := sorry

/-- An arbitrary ringed-topos morphism is an equivalence when its underlying inverse image is an
equivalence and its inverse-image structure-sheaf map is an isomorphism. -/
@[stacks 03CR "ringed equivalence"]
class IsEquivalence (f : ToposHom X Y) : Prop where
  /-- The inverse image of the underlying morphism of topoi is an equivalence. -/
  inverseImage_isEquivalence : Functor.IsEquivalence f.toTopos.inverseImage
  /-- The inverse-image structure-sheaf map is an isomorphism. -/
  structureMap_isIso : IsIso f.structureMap

/-- The identity morphism is a ringed equivalence. -/
theorem id_isEquivalence (X : RingedSite.{uX, vX, w})
    [X.siteTopology.HasSheafCompose (forget RingCat.{w})] :
    (id X).IsEquivalence := sorry

/-- The composite of two morphisms of site-presented ringed topoi. -/
@[stacks 01D3 "(3), arbitrary"]
noncomputable def comp (f : ToposHom X Y) (g : ToposHom Y Z) : ToposHom X Z where
  toTopos := MorphismOfTopoiIn.comp g.toTopos f.toTopos
  structureMap :=
    (MorphismOfTopoiIn.ringInverseImageCompIso g.toTopos f.toTopos).hom.app
        Z.structureSheaf ≫
      f.toTopos.ringInverseImage.map g.structureMap ≫ f.structureMap

-- Every non-Prop field is an explicit inverse-image map or a mate under the canonical
-- internal-ring adjunction; no ring-valued direct-image choice remains in `ToposHom`.

end ToposHom

end RingedSite
