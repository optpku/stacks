/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Adjunction.Mates
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Pushforward
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Underlying
public import ReasLib.AlgebraicGeometry.RingedSite.Fibered.Inherited.Morphism
public import ReasLib.CategoryTheory.Fibered.CategoryOver
public import ReasLib.CategoryTheory.Fibered.InheritedTopology.Projection
public import ReasLib.CategoryTheory.Sites.AbelianSheaf.Additive
import Mathlib.Tactic.CrossRefAttribute

/-!
# Lower shriek for inherited sites of fibered categories

This leaf owns the abelian and module inverse-image/lower-shriek functors attached to a morphism
of fibered categories over a ringed site.  It is the reusable counterpart of the Chapter 21
setup; no chapter module is imported here.
-/

@[expose] public section

open CategoryTheory
open RingedSite.Hom
open scoped RingedSite.Hom

noncomputable section

universe u v w vS z

namespace CategoryTheory.FiberedCategoryOver

section Abelian

variable {D : RingedSite.{u, v}}
variable {C C' : FiberedCategoryOver.{u, v, w, vS} D.carrier}

/-- The inherited topology of a fibered category over a ringed site. -/
@[stacks 08PC "inherited topology of a fibered category"]
abbrev sourceTopology (D : RingedSite.{u, v})
    (C : FiberedCategoryOver.{u, v, w, vS} D.carrier) :
    GrothendieckTopology C.total :=
  C.p.inheritedTopology D.siteTopology

/-- The abelian-sheaf inverse-image functor attached to a continuous morphism of inherited sites. -/
@[stacks 08PC "abelian inverse image for a fibered-category morphism"]
noncomputable abbrev abelianInverseImage (u : C' ⟶ C)
    [Functor.IsContinuous (toFunctor u) (sourceTopology D C') (sourceTopology D C)] :
    Sheaf (sourceTopology D C) AddCommGrpCat.{z} ⥤
      Sheaf (sourceTopology D C') AddCommGrpCat.{z} :=
  (toFunctor u).sheafPushforwardContinuous
    AddCommGrpCat.{z} (sourceTopology D C') (sourceTopology D C)

namespace abelianInverseImage

/-- Lemma 21.38.5 (08PC), ordinary part: inverse image on abelian sheaves for a morphism of
fibered categories admits a left adjoint when both total categories are essentially small
in the coefficient universe. The adjunction is transported from left Kan extension and
sheafification on small models; cocontinuity is only needed for its geometric interpretation. -/
@[stacks 08PC "(1) abelian lower-shriek existence", instance]
theorem isRightAdjoint (u : C' ⟶ C)
    [EssentiallySmall.{z} C.total] [EssentiallySmall.{z} C'.total]
    [Functor.IsContinuous (toFunctor u) (sourceTopology D C') (sourceTopology D C)]
    [Functor.IsCocontinuous (toFunctor u) (sourceTopology D C') (sourceTopology D C)] :
    Functor.IsRightAdjoint (abelianInverseImage u :
      Sheaf (sourceTopology D C) AddCommGrpCat.{z} ⥤
        Sheaf (sourceTopology D C') AddCommGrpCat.{z}) := by
  let c := equivSmallModel.{z} C.total
  let c' := equivSmallModel.{z} C'.total
  let J := sourceTopology D C
  let J' := sourceTopology D C'
  let K := c.inverse.inducedTopology J
  let K' := c'.inverse.inducedTopology J'
  letI : (toFunctor u ⋙ c.functor).IsContinuous J' K :=
    Functor.isContinuous_comp (toFunctor u) c.functor J' J K
  let H := c'.inverse ⋙ toFunctor u ⋙ c.functor
  letI : H.IsContinuous K' K :=
    Functor.isContinuous_comp c'.inverse (toFunctor u ⋙ c.functor) K' J' K
  let E := c.sheafCongr J K AddCommGrpCat.{z}
  let E' := c'.sheafCongr J' K' AddCommGrpCat.{z}
  let comparison :
      (E.inverse ⋙ abelianInverseImage u) ⋙ E'.functor ≅
        H.sheafPushforwardContinuous AddCommGrpCat.{z} K' K := Iso.refl _
  letI : (H.sheafPushforwardContinuous AddCommGrpCat.{z} K' K).IsRightAdjoint :=
    inferInstance
  letI : ((E.inverse ⋙ abelianInverseImage u) ⋙ E'.functor).IsRightAdjoint :=
    Functor.isRightAdjoint_of_iso comparison.symm
  letI : (E.inverse ⋙ abelianInverseImage u).IsRightAdjoint :=
    (Functor.isRightAdjoint_comp_iff_left _ E'.functor).mp inferInstance
  exact (Functor.isRightAdjoint_comp_iff_right E.inverse _).mp inferInstance

end abelianInverseImage

/-- The abelian lower-shriek functor, once its inverse image is a right adjoint. -/
@[stacks 08PC "(1) abelian lower shriek for a fibered-category morphism"]
noncomputable abbrev abelianLowerShriek (u : C' ⟶ C)
    [EssentiallySmall.{z} C.total] [EssentiallySmall.{z} C'.total]
    [Functor.IsContinuous (toFunctor u) (sourceTopology D C') (sourceTopology D C)]
    [Functor.IsCocontinuous (toFunctor u) (sourceTopology D C') (sourceTopology D C)] :
    Sheaf (sourceTopology D C') AddCommGrpCat.{z} ⥤
      Sheaf (sourceTopology D C) AddCommGrpCat.{z} :=
  Functor.leftAdjoint (abelianInverseImage u)

end Abelian

section Module

variable {D : RingedSite.{u, v}}
variable {C C' : FiberedCategoryOver.{u, v, u, v} D.carrier}

/-- The module-sheaf inverse-image functor attached to a fibered-category morphism. -/
@[stacks 08PC "module inverse image for a fibered-category morphism"]
def moduleInverseImage (u : C' ⟶ C)
    [IsMorphismOfSites
      (C'.p.inheritedTopology D.siteTopology)
      (C.p.inheritedTopology D.siteTopology)
      (toFunctor u)] :
    SheafOfModules C.p.inheritedRingedSite.structureSheaf ⥤
      SheafOfModules C'.p.inheritedRingedSite.structureSheaf :=
  RingedSite.Hom.modulePushforward
    (Functor.inheritedRingedSiteHom (p := C.p) (p' := C'.p)
      (toFunctor u) (comm u))

namespace moduleInverseImage

/-- Lemma 21.38.5 (08PC), ordinary part: inverse image on module sheaves for a morphism of
fibered categories admits a left adjoint when the site and coefficient universes
fit in the module section universe. -/
@[stacks 08PC "(1) module lower-shriek existence", instance]
theorem isRightAdjoint (u : C' ⟶ C)
    [UnivLE.{max u v, z}]
    [IsMorphismOfSites
      (C'.p.inheritedTopology D.siteTopology)
      (C.p.inheritedTopology D.siteTopology)
      (toFunctor u)]
    [Functor.IsCocontinuous
      (toFunctor u)
      (C'.p.inheritedTopology D.siteTopology)
      (C.p.inheritedTopology D.siteTopology)] :
    Functor.IsRightAdjoint (moduleInverseImage.{u, v, z} u) := sorry

end moduleInverseImage

/-- Forgetting module structure after `moduleInverseImage u` agrees with `abelianInverseImage u`. -/
@[stacks 08PC "(2) underlying abelian inverse-image comparison"]
theorem moduleInverseImage_comp_underlyingAbelianSheafFunctor (u : C' ⟶ C)
    [IsMorphismOfSites
      (C'.p.inheritedTopology D.siteTopology)
      (C.p.inheritedTopology D.siteTopology)
      (toFunctor u)] :
    moduleInverseImage u ⋙
        underlyingAbelianSheafFunctor C'.p.inheritedRingedSite =
      underlyingAbelianSheafFunctor C.p.inheritedRingedSite ⋙
        abelianInverseImage u := sorry

/-- The canonical isomorphism form of the underived forgetful comparison. -/
@[stacks 08PC "underlying abelian inverse-image comparison isomorphism"]
noncomputable def moduleInverseImageUnderlyingIso (u : C' ⟶ C)
    [IsMorphismOfSites
      (C'.p.inheritedTopology D.siteTopology)
      (C.p.inheritedTopology D.siteTopology)
      (toFunctor u)] :
    moduleInverseImage u ⋙
        underlyingAbelianSheafFunctor C'.p.inheritedRingedSite ≅
      underlyingAbelianSheafFunctor C.p.inheritedRingedSite ⋙
        abelianInverseImage u :=
  Iso.refl _

/-- The module lower-shriek functor, once the module inverse image is a right adjoint. -/
@[stacks 08PC "(1) module lower shriek for a fibered-category morphism"]
def moduleLowerShriek (u : C' ⟶ C)
    [UnivLE.{max u v, z}]
    [IsMorphismOfSites
      (C'.p.inheritedTopology D.siteTopology)
      (C.p.inheritedTopology D.siteTopology)
      (toFunctor u)]
    [Functor.IsCocontinuous
      (toFunctor u)
      (C'.p.inheritedTopology D.siteTopology)
      (C.p.inheritedTopology D.siteTopology)] :
    SheafOfModules.{z} C'.p.inheritedRingedSite.structureSheaf ⥤
      SheafOfModules.{z} C.p.inheritedRingedSite.structureSheaf :=
  Functor.leftAdjoint (moduleInverseImage u)

/-- The mate comparison between the abelian and module lower shrieks after forgetting module
structure. -/
@[stacks 08PC "(2) module and abelian lower-shriek comparison"]
noncomputable def lowerShriekForgetComparison (u : C' ⟶ C)
    [UnivLE.{max u v, z}]
    [EssentiallySmall.{z} C.total] [EssentiallySmall.{z} C'.total]
    [IsMorphismOfSites
      (C'.p.inheritedTopology D.siteTopology)
      (C.p.inheritedTopology D.siteTopology)
      (toFunctor u)]
    [Functor.IsCocontinuous
      (toFunctor u)
      (C'.p.inheritedTopology D.siteTopology)
      (C.p.inheritedTopology D.siteTopology)] :
    underlyingAbelianSheafFunctor.{z} C'.p.inheritedRingedSite ⋙
        abelianLowerShriek u ⟶
      moduleLowerShriek u ⋙
        underlyingAbelianSheafFunctor.{z} C.p.inheritedRingedSite :=
  let square :
      TwoSquare
        (moduleInverseImage u)
        (underlyingAbelianSheafFunctor.{z} C.p.inheritedRingedSite)
        (underlyingAbelianSheafFunctor.{z} C'.p.inheritedRingedSite)
        (abelianInverseImage u) :=
    TwoSquare.mk
      (moduleInverseImage u)
      (underlyingAbelianSheafFunctor.{z} C.p.inheritedRingedSite)
      (underlyingAbelianSheafFunctor.{z} C'.p.inheritedRingedSite)
      (abelianInverseImage u)
      (moduleInverseImageUnderlyingIso u).hom
  ((mateEquiv
        (Adjunction.ofIsRightAdjoint (moduleInverseImage u))
        (Adjunction.ofIsRightAdjoint (abelianInverseImage u))).symm
        square).natTrans

/-- The module/abelian lower-shriek comparison is an isomorphism. -/
@[stacks 08PC "(2) commutation with the forgetful functor"]
instance lowerShriekForgetComparison_isIso (u : C' ⟶ C)
    [UnivLE.{max u v, z}]
    [EssentiallySmall.{z} C.total] [EssentiallySmall.{z} C'.total]
    [IsMorphismOfSites
      (C'.p.inheritedTopology D.siteTopology)
      (C.p.inheritedTopology D.siteTopology)
      (toFunctor u)]
    [Functor.IsCocontinuous
      (toFunctor u)
      (C'.p.inheritedTopology D.siteTopology)
      (C.p.inheritedTopology D.siteTopology)] :
    IsIso (lowerShriekForgetComparison.{u, v, z} u) := sorry

end Module

-- The comparison isomorphism is the identity on the explicit underlying functors; it does not
-- turn the deferred equality theorem into non-Prop data.

end CategoryTheory.FiberedCategoryOver
