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
    [@GrothendieckTopology.HasSheafCompose X.carrier X.carrier.str RingCat.{w} inferInstance (Type w) inferInstance X.siteTopology (forget RingCat.{w})]
    [@GrothendieckTopology.HasSheafCompose Y.carrier Y.carrier.str RingCat.{w} inferInstance (Type w) inferInstance Y.siteTopology (forget RingCat.{w})] where
  /-- The underlying morphism of topoi. -/
  toTopos : @MorphismOfTopoiIn.{uY, uX, vY, vX, w} Y.carrier Y.carrier.str X.carrier X.carrier.str
    Y.siteTopology X.siteTopology
  /-- The inverse-image-form structure-sheaf map `f⁻¹𝒪_Y ⟶ 𝒪_X`. -/
  structureMap :
    (@MorphismOfTopoiIn.ringInverseImage Y.carrier Y.carrier.str X.carrier X.carrier.str Y.siteTopology X.siteTopology toTopos inferInstance inferInstance).obj Y.structureSheaf ⟶ X.structureSheaf

namespace ToposHom

variable {X : RingedSite.{uX, vX, w}} {Y : RingedSite.{uY, vY, w}}
  {Z : RingedSite.{uZ, vZ, w}}
variable [@GrothendieckTopology.HasSheafCompose X.carrier X.carrier.str RingCat.{w} inferInstance (Type w) inferInstance X.siteTopology (forget RingCat.{w})]
  [@GrothendieckTopology.HasSheafCompose Y.carrier Y.carrier.str RingCat.{w} inferInstance (Type w) inferInstance Y.siteTopology (forget RingCat.{w})]
  [@GrothendieckTopology.HasSheafCompose Z.carrier Z.carrier.str RingCat.{w} inferInstance (Type w) inferInstance Z.siteTopology (forget RingCat.{w})]

namespace Direct

open CategoryTheory.Sheaf.InternalRing

variable (toTopos : @MorphismOfTopoiIn.{uY, uX, vY, vX, w} Y.carrier Y.carrier.str X.carrier X.carrier.str
  Y.siteTopology X.siteTopology)
variable (ringPushforward :
  (@Sheaf X.carrier X.carrier.str X.siteTopology RingCat.{w} inferInstance) ⥤ (@Sheaf Y.carrier Y.carrier.str Y.siteTopology RingCat.{w} inferInstance))
variable (forgetIso :
  ringPushforward ⋙ (@sheafCompose Y.carrier Y.carrier.str RingCat.{w} inferInstance (Type w) inferInstance Y.siteTopology (forget RingCat.{w}) inferInstance) ≅
    (@sheafCompose X.carrier X.carrier.str RingCat.{w} inferInstance (Type w) inferInstance X.siteTopology (forget RingCat.{w}) inferInstance) ⋙ toTopos.pushforward)
variable (structureMap : Y.structureSheaf ⟶ ringPushforward.obj X.structureSheaf)

/-- The underlying type-valued direct-image map supplied by a direct-image presentation. -/
abbrev underlyingMap : Hom.underlyingStructureSheaf Y ⟶
    toTopos.pushforward.obj (Hom.underlyingStructureSheaf X) :=
  ((@sheafCompose Y.carrier Y.carrier.str RingCat.{w} inferInstance (Type w) inferInstance Y.siteTopology (forget RingCat.{w}) inferInstance)).map structureMap ≫
    forgetIso.hom.app X.structureSheaf

/-- A direct-image presentation is ring-compatible when its underlying structure map preserves
the canonical internal-ring operations on direct image. -/
abbrev IsRingCompatible : Prop :=
  @IsRingHom ((@Sheaf Y.carrier Y.carrier.str Y.siteTopology (Type w) inferInstance)) _ _
    (@RingObjects.carrier Y.carrier Y.carrier.str Y.siteTopology ((@toInternal Y.carrier Y.carrier.str Y.siteTopology inferInstance).obj Y.structureSheaf))
    (@RingObjects.carrier Y.carrier Y.carrier.str Y.siteTopology
      ((@MorphismOfTopoiIn.internalRingDirectImage Y.carrier Y.carrier.str X.carrier X.carrier.str Y.siteTopology X.siteTopology toTopos).obj ((@toInternal X.carrier X.carrier.str X.siteTopology inferInstance).obj X.structureSheaf)))
    (@RingObjects.ringObj Y.carrier Y.carrier.str Y.siteTopology
      ((@toInternal Y.carrier Y.carrier.str Y.siteTopology inferInstance).obj Y.structureSheaf)).toAddGrpObj.toAddMonObj
    (@RingObjects.ringObj Y.carrier Y.carrier.str Y.siteTopology
      ((@MorphismOfTopoiIn.internalRingDirectImage Y.carrier Y.carrier.str X.carrier X.carrier.str Y.siteTopology X.siteTopology toTopos).obj
        ((@toInternal X.carrier X.carrier.str X.siteTopology inferInstance).obj X.structureSheaf))).toAddGrpObj.toAddMonObj
    (@RingObjects.ringObj Y.carrier Y.carrier.str Y.siteTopology ((@toInternal Y.carrier Y.carrier.str Y.siteTopology inferInstance).obj Y.structureSheaf)).toMonObj
    (@RingObjects.ringObj Y.carrier Y.carrier.str Y.siteTopology
      ((@MorphismOfTopoiIn.internalRingDirectImage Y.carrier Y.carrier.str X.carrier X.carrier.str Y.siteTopology X.siteTopology toTopos).obj ((@toInternal X.carrier X.carrier.str X.siteTopology inferInstance).obj X.structureSheaf))).toMonObj
    (underlyingMap toTopos ringPushforward forgetIso structureMap)

/-- The internal-ring direct-image morphism associated to a compatible direct presentation. -/
noncomputable def internalMap
    (h : IsRingCompatible toTopos ringPushforward forgetIso structureMap) :
    @RingObjects.Hom Y.carrier Y.carrier.str Y.siteTopology ((@toInternal Y.carrier Y.carrier.str Y.siteTopology inferInstance).obj Y.structureSheaf)
      ((@MorphismOfTopoiIn.internalRingDirectImage Y.carrier Y.carrier.str X.carrier X.carrier.str Y.siteTopology X.siteTopology toTopos).obj ((@toInternal X.carrier X.carrier.str X.siteTopology inferInstance).obj X.structureSheaf)) :=
  @RingObjCat.Hom.mk ((@Sheaf Y.carrier Y.carrier.str Y.siteTopology (Type w) inferInstance)) _ _
    (@sheafBraidedCategory Y.carrier Y.carrier.str Y.siteTopology) _ _
    (underlyingMap toTopos ringPushforward forgetIso structureMap) h

/-- The internal-ring inverse-image mate of a compatible direct presentation. -/
noncomputable def inverseMap
    (h : IsRingCompatible toTopos ringPushforward forgetIso structureMap) :
    @RingObjects.Hom X.carrier X.carrier.str X.siteTopology
      ((@MorphismOfTopoiIn.internalRingInverseImage Y.carrier Y.carrier.str X.carrier X.carrier.str Y.siteTopology X.siteTopology toTopos).obj ((@toInternal Y.carrier Y.carrier.str Y.siteTopology inferInstance).obj Y.structureSheaf))
      ((@toInternal X.carrier X.carrier.str X.siteTopology inferInstance).obj X.structureSheaf) :=
  ((@MorphismOfTopoiIn.internalRingAdjunction Y.carrier Y.carrier.str X.carrier X.carrier.str Y.siteTopology X.siteTopology toTopos).homEquiv _ _).symm
    (internalMap toTopos ringPushforward forgetIso structureMap h)

/-- The canonical ring-valued inverse-image structure map reconstructed from a compatible
direct presentation. -/
noncomputable def inverseStructureMap
    (h : IsRingCompatible toTopos ringPushforward forgetIso structureMap) :
    (@MorphismOfTopoiIn.ringInverseImage Y.carrier Y.carrier.str X.carrier X.carrier.str Y.siteTopology X.siteTopology toTopos inferInstance inferInstance).obj Y.structureSheaf ⟶ X.structureSheaf :=
  (@fromInternal X.carrier X.carrier.str X.siteTopology).map (inverseMap toTopos ringPushforward forgetIso structureMap h) ≫
    (@toFromIso X.carrier X.carrier.str X.siteTopology inferInstance).hom.app X.structureSheaf

end Direct

/-- Construct a ringed-topos morphism from a compatible direct-image presentation.  The
auxiliary direct-image functor is used only to form the canonical inverse-image mate. -/
noncomputable def ofDirectImage
    (toTopos : @MorphismOfTopoiIn.{uY, uX, vY, vX, w} Y.carrier Y.carrier.str X.carrier X.carrier.str
      Y.siteTopology X.siteTopology)
    (ringPushforward :
      (@Sheaf X.carrier X.carrier.str X.siteTopology RingCat.{w} inferInstance) ⥤ (@Sheaf Y.carrier Y.carrier.str Y.siteTopology RingCat.{w} inferInstance))
    (forgetIso :
      ringPushforward ⋙ (@sheafCompose Y.carrier Y.carrier.str RingCat.{w} inferInstance (Type w) inferInstance Y.siteTopology (forget RingCat.{w}) inferInstance) ≅
        (@sheafCompose X.carrier X.carrier.str RingCat.{w} inferInstance (Type w) inferInstance X.siteTopology (forget RingCat.{w}) inferInstance) ⋙ toTopos.pushforward)
    (structureMap : Y.structureSheaf ⟶ ringPushforward.obj X.structureSheaf)
    (h : Direct.IsRingCompatible toTopos ringPushforward forgetIso structureMap) :
    ToposHom X Y where
  toTopos := toTopos
  structureMap := Direct.inverseStructureMap
    toTopos ringPushforward forgetIso structureMap h

/-- The identity morphism of a site-presented ringed topos. -/
noncomputable def id (X : RingedSite.{uX, vX, w})
    [@GrothendieckTopology.HasSheafCompose X.carrier X.carrier.str RingCat.{w} inferInstance (Type w) inferInstance X.siteTopology (forget RingCat.{w})] : ToposHom X X where
  toTopos := @MorphismOfTopoiIn.id X.carrier X.carrier.str X.siteTopology
  structureMap :=
    (@MorphismOfTopoiIn.ringInverseImageIdIso X.carrier X.carrier.str X.siteTopology inferInstance).hom.app X.structureSheaf

/-- The inverse-image structure-sheaf map after forgetting to type-valued sheaves. -/
noncomputable abbrev underlyingMap (f : ToposHom X Y) :
    f.toTopos.inverseImage.obj (Hom.underlyingStructureSheaf Y) ⟶
      Hom.underlyingStructureSheaf X :=
  (@MorphismOfTopoiIn.ringInverseImageForgetIso Y.carrier Y.carrier.str X.carrier X.carrier.str Y.siteTopology X.siteTopology f.toTopos inferInstance inferInstance).inv.app Y.structureSheaf ≫
    ((@sheafCompose X.carrier X.carrier.str RingCat.{w} inferInstance (Type w) inferInstance X.siteTopology (forget RingCat.{w}) inferInstance)).map f.structureMap

/-- The direct-image form of the structure-sheaf map, obtained from the canonical ring-valued
adjunction. -/
noncomputable def directStructureMap (f : ToposHom X Y) :
    Y.structureSheaf ⟶ (@MorphismOfTopoiIn.ringDirectImage Y.carrier Y.carrier.str X.carrier X.carrier.str Y.siteTopology X.siteTopology f.toTopos inferInstance inferInstance).obj X.structureSheaf :=
  ((@MorphismOfTopoiIn.ringAdjunction Y.carrier Y.carrier.str X.carrier X.carrier.str Y.siteTopology X.siteTopology f.toTopos inferInstance inferInstance).homEquiv _ _) f.structureMap

/-- The direct-image structure-sheaf map after forgetting to type-valued sheaves. -/
noncomputable abbrev underlyingDirectImageMap (f : ToposHom X Y) :
    Hom.underlyingStructureSheaf Y ⟶
      f.toTopos.pushforward.obj (Hom.underlyingStructureSheaf X) :=
  ((@sheafCompose Y.carrier Y.carrier.str RingCat.{w} inferInstance (Type w) inferInstance Y.siteTopology (forget RingCat.{w}) inferInstance)).map f.directStructureMap ≫
    (@MorphismOfTopoiIn.ringDirectImageForgetIso Y.carrier Y.carrier.str X.carrier X.carrier.str Y.siteTopology X.siteTopology f.toTopos inferInstance inferInstance).hom.app X.structureSheaf

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
    [@GrothendieckTopology.HasSheafCompose X.carrier X.carrier.str RingCat.{w} inferInstance (Type w) inferInstance X.siteTopology (forget RingCat.{w})] :
    (id X).IsEquivalence := sorry

/-- The composite of two morphisms of site-presented ringed topoi. -/
@[stacks 01D3 "(3), arbitrary"]
noncomputable abbrev comp (f : ToposHom X Y) (g : ToposHom Y Z) : ToposHom X Z where
  toTopos := @MorphismOfTopoiIn.comp Z.carrier Z.carrier.str Y.carrier Y.carrier.str Z.siteTopology Y.siteTopology X.carrier X.carrier.str X.siteTopology g.toTopos f.toTopos
  structureMap :=
    (@MorphismOfTopoiIn.ringInverseImageCompIso Z.carrier Z.carrier.str Y.carrier Y.carrier.str X.carrier X.carrier.str Z.siteTopology Y.siteTopology X.siteTopology g.toTopos f.toTopos inferInstance inferInstance inferInstance).hom.app
        Z.structureSheaf ≫
      (@MorphismOfTopoiIn.ringInverseImage Y.carrier Y.carrier.str X.carrier X.carrier.str Y.siteTopology X.siteTopology f.toTopos inferInstance inferInstance).map g.structureMap ≫ f.structureMap

-- Every non-Prop field is an explicit inverse-image map or a mate under the canonical
-- internal-ring adjunction; no ring-valued direct-image choice remains in `ToposHom`.

end ToposHom

end RingedSite
