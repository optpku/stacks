/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Adjunction.Whiskering
public import Mathlib.CategoryTheory.Comma.Over.Pullback
public import Mathlib.CategoryTheory.MorphismProperty.OverAdjunction
public import Mathlib.CategoryTheory.Sites.LeftExact
public import ReasLib.CategoryTheory.Functor.SectionsTerminal
public import ReasLib.CategoryTheory.Sites.Topos.Sections
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSite.RestrictionTopos
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSite.IdentityRelocalization
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Ph.Site
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.LocalAtTarget.BaseChange
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Fppf.Comparison
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Sites.FpqcPrecoverage

/-!
# Small-to-big étale sections of algebraic spaces

Objectwise, inverse image along `π_X` is identified with global sections of
small-site pullback. The same underlying presheaf satisfies the sheaf condition
for the smooth, syntomic, fppf, fpqc, and ph topologies on `Over X`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Functor Opposite
open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open scoped MorphismOfTopoiIn

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Etale.SmallToBig

variable {S : Scheme.{u}}

/-- Spaces étale pullback followed by relocalization is continuous into
`(Spaces/X)_étale`. -/
private instance spacesPullback_relocalization_isContinuous {X Y : AlgebraicSpace S} (f : Y ⟶ X) :
    (spacesEtalePullback f ⋙ Etale.SpacesToBig.relocalizationFunctor f).IsContinuous
      (spacesEtaleTopology X) (overEtaleTopology X) :=
  Functor.isContinuous_comp (spacesEtalePullback f)
    (Etale.SpacesToBig.relocalizationFunctor f)
    (spacesEtaleTopology X) (spacesEtaleTopology Y) (overEtaleTopology X)

/-- The pullback projection maps relocalized base changes to their original objects. -/
private def pullbackRelocalizationToIdentity {X Y : AlgebraicSpace S} (f : Y ⟶ X) :
    spacesEtalePullback f ⋙ Etale.SpacesToBig.relocalizationFunctor f ⟶
      Etale.SpacesToBig.relocalizationFunctor (𝟙 X) :=
  (associator (spacesEtalePullback f)
    (MorphismProperty.Over.forget (@Etale S) ⊤ Y) (Over.map f)).inv ≫
    whiskerRight (MorphismProperty.Over.pullbackCompForgetIso
      (P := @Etale S) (Q := ⊤) f).hom (Over.map f) ≫
    (associator (MorphismProperty.Over.forget (@Etale S) ⊤ X)
      (Over.pullback f) (Over.map f)).hom ≫
    whiskerLeft (MorphismProperty.Over.forget (@Etale S) ⊤ X)
      (Over.mapPullbackAdj f).counit ≫
    whiskerLeft (MorphismProperty.Over.forget (@Etale S) ⊤ X) (Over.mapId X).inv

/-- Restriction to the spaces étale site maps naturally to restriction after base change. -/
private def restrictionComparison {X Y : AlgebraicSpace S} (f : Y ⟶ X) :
    Etale.SpacesToBig.inverseImage.{u, u + 1} (𝟙 X) ⟶
      Etale.SpacesToBig.inverseImage.{u, u + 1} f ⋙ (spacesEtaleMorphismOfTopoi f).pushforward :=
  sheafPushforwardContinuousNatTrans (pullbackRelocalizationToIdentity f) (Type (u + 1))
      (spacesEtaleTopology X) (overEtaleTopology X) ≫
    (sheafPushforwardContinuousComp (spacesEtalePullback f)
      (Etale.SpacesToBig.relocalizationFunctor f) (Type (u + 1))
      (spacesEtaleTopology X) (spacesEtaleTopology Y) (overEtaleTopology X)).inv

/-- Spaces-étale inverse image maps naturally to restriction of big-site inverse image. -/
private def inverseImageComparison {X Y : AlgebraicSpace S} (f : Y ⟶ X) :
    (spacesEtaleMorphismOfTopoi f)⁻¹ ⟶
      Etale.SpacesToBig.lowerShriek.{u, u + 1} (𝟙 X) ⋙ Etale.SpacesToBig.inverseImage.{u, u + 1} f :=
  (((spacesEtaleMorphismOfTopoi f).adjunction.whiskerRight
    (Sheaf (spacesEtaleTopology X) (Type (u + 1)))).homEquiv
      (𝟭 _) (Etale.SpacesToBig.lowerShriek.{u, u + 1} (𝟙 X) ⋙ Etale.SpacesToBig.inverseImage.{u, u + 1} f)).symm
    (((Etale.SpacesToBig.relocalizationFunctor (𝟙 X)).sheafAdjunctionContinuous (Type (u + 1))
        (spacesEtaleTopology X) (overEtaleTopology X)).unit ≫
      whiskerLeft (Etale.SpacesToBig.lowerShriek.{u, u + 1} (𝟙 X)) (restrictionComparison f) ≫
      (associator (Etale.SpacesToBig.lowerShriek.{u, u + 1} (𝟙 X)) (Etale.SpacesToBig.inverseImage.{u, u + 1} f)
        (spacesEtaleMorphismOfTopoi f).pushforward).inv)

/-- Spaces identity pullback of `i_* F` maps to small-to-big inverse image of `F`. -/
private def spacesIdPullbackToPiInverse {X : AlgebraicSpace S}
    (F : Sheaf (smallEtaleTopology X) (Type (u + 1))) :
    (Etale.SpacesToBig.lowerShriek.{u, u + 1} (𝟙 X)).obj
      ((smallEtaleInclusionInverseMorphismOfTopoi X).inverseImage.obj F) ⟶
      ((siteMorphismOfTopoi X)⁻¹).obj F :=
  let FX := (smallEtaleInclusionInverseMorphismOfTopoi X).inverseImage.obj F
  let πF := ((siteMorphismOfTopoi X)⁻¹).obj F
  let restrictComp :=
    sheafPushforwardContinuousComp (smallEtaleToSpaces X)
      (Etale.SpacesToBig.relocalizationFunctor (𝟙 X)) (Type (u + 1))
      (smallEtaleTopology X) (spacesEtaleTopology X) (overEtaleTopology X)
  let restrictIso :=
    smallEtaleInclusionDirectImage_inv_sheafPushforwardContinuous X
  (((Etale.SpacesToBig.relocalizationFunctor (𝟙 X)).sheafAdjunctionContinuous (Type (u + 1))
      (spacesEtaleTopology X) (overEtaleTopology X)).homEquiv FX πF).symm
    ((smallEtaleInclusionDirectImage X).map
        ((siteMorphismOfTopoi X).adjunction.unit.app F) ≫
      (smallEtaleInclusionDirectImage X).map (restrictComp.inv.app πF) ≫
      (smallEtaleInclusionDirectImage X).map
        (restrictIso.inv.app ((Etale.SpacesToBig.inverseImage.{u, u + 1} (𝟙 X)).obj πF)) ≫
      (smallEtalePresentationEquivalence X).counitIso.hom.app
        ((Etale.SpacesToBig.inverseImage.{u, u + 1} (𝟙 X)).obj πF))

/-- Relocalization of the identity object of `Y_spaces,étale` is `Over.mk f`. -/
private def relocalizationSelfIso {X Y : AlgebraicSpace S} (f : Y ⟶ X) :
    (Etale.SpacesToBig.relocalizationFunctor f).obj (spacesEtaleSite.self Y) ≅
      Over.mk f :=
  Over.isoMk (Iso.refl Y) rfl

/-- Global sections of `f_small⁻¹ F` map canonically to big-site inverse-image sections. -/
@[no_expose]
def sectionsComparison {X Y : AlgebraicSpace S} (f : Y ⟶ X)
    (F : Sheaf (smallEtaleTopology X) (Type (u + 1))) :
    ((smallEtaleMorphismOfTopoi f).inverseImage.obj F).obj.sections →
      (((siteMorphismOfTopoi X)⁻¹).obj F).1.obj (op (Over.mk f)) :=
  fun sectionValue ↦
    let FX := (smallEtaleInclusionInverseMorphismOfTopoi X).inverseImage.obj F
    let H := (spacesEtaleMorphismOfTopoi f).inverseImage.obj FX
    let G := (smallEtaleMorphismOfTopoi f).inverseImage.obj F
    let s1 :=
      ((smallEtaleInclusionMorphismOfTopoi Y).pushforwardSectionsEquiv G).symm sectionValue
    let s2 :=
      (sectionsFunctor _).map
        ((smallEtalePresentationEquivalence Y).counitIso.app H).hom.hom s1
    let s3 :=
      (sectionsFunctor _).map ((inverseImageComparison f).app FX).hom s2
    let s4 :=
      sectionsEquivTerminal
        (((Etale.SpacesToBig.inverseImage.{u, u + 1} f).obj ((Etale.SpacesToBig.lowerShriek.{u, u + 1} (𝟙 X)).obj FX)).obj)
        (spacesEtaleSite.self Y) (isTerminal_self Y) s3
    (spacesIdPullbackToPiInverse F).hom.app (op (Over.mk f))
      (((Etale.SpacesToBig.lowerShriek.{u, u + 1} (𝟙 X)).obj FX).1.map (relocalizationSelfIso f).inv.op
        ((Etale.SpacesToBig.inverseImage_objObjIso f ((Etale.SpacesToBig.lowerShriek.{u, u + 1} (𝟙 X)).obj FX)
            (spacesEtaleSite.self Y)).hom s4))

/-- The canonical comparison identifies small-site global sections with big-site sections. -/
theorem sectionsComparison_bijective {X Y : AlgebraicSpace S} (f : Y ⟶ X)
    (F : Sheaf (smallEtaleTopology X) (Type (u + 1))) :
    Function.Bijective (sectionsComparison f F) :=
  sorry

/-- Small-to-big inverse image of an étale sheaf satisfies the sheaf condition for
smooth coverings. -/
theorem inverseImage_isSheaf_smooth {X : AlgebraicSpace S}
    (F : Sheaf (smallEtaleTopology X) (Type (u + 1))) :
    Presheaf.IsSheaf ((smoothPrecoverage S).toGrothendieck.over X)
      (((siteMorphismOfTopoi X)⁻¹).obj F).1 :=
  sorry

/-- Small-to-big inverse image of an étale sheaf satisfies the sheaf condition for
syntomic coverings. -/
theorem inverseImage_isSheaf_syntomic {X : AlgebraicSpace S}
    (F : Sheaf (smallEtaleTopology X) (Type (u + 1))) :
    Presheaf.IsSheaf ((syntomicPrecoverage S).toGrothendieck.over X)
      (((siteMorphismOfTopoi X)⁻¹).obj F).1 :=
  sorry

/-- Small-to-big inverse image of an étale sheaf satisfies the sheaf condition for
fppf coverings. -/
theorem inverseImage_isSheaf_fppf {X : AlgebraicSpace S}
    (F : Sheaf (smallEtaleTopology X) (Type (u + 1))) :
    Presheaf.IsSheaf (overFppfTopology X)
      (((siteMorphismOfTopoi X)⁻¹).obj F).1 :=
  sorry

/-- Small-to-big inverse image of an étale sheaf satisfies the sheaf condition for
fpqc coverings. -/
theorem inverseImage_isSheaf_fpqc {X : AlgebraicSpace S}
    (F : Sheaf (smallEtaleTopology X) (Type (u + 1))) :
    Presheaf.IsSheaf ((fpqcPrecoverage S).toGrothendieck.over X)
      (((siteMorphismOfTopoi X)⁻¹).obj F).1 :=
  sorry

/-- Small-to-big inverse image of an étale sheaf satisfies the sheaf condition for
ph coverings. -/
theorem inverseImage_isSheaf_ph {X : AlgebraicSpace S}
    (F : Sheaf (smallEtaleTopology X) (Type (u + 1))) :
    Presheaf.IsSheaf (bigPhSite X)
      (((siteMorphismOfTopoi X)⁻¹).obj F).1 :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Etale.SmallToBig

end

end
