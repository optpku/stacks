/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Adjunction.Whiskering
public import Mathlib.CategoryTheory.Comma.Over.Pullback
public import Mathlib.CategoryTheory.MorphismProperty.OverAdjunction
public import Mathlib.CategoryTheory.Sites.LeftExact
public import ReasLib.CategoryTheory.Functor.SectionsTerminal
public import ReasLib.CategoryTheory.Sites.Topos.Sections
public import stacks_project.Chap66.Lemma_66_18_8_Topos
public import stacks_project.Chap66.Lemma_66_18_11
public import stacks_project.Chap73.Lemma_73_4_7_Relocalization
public import stacks_project.Chap73.Lemma_73_4_8_Identity
public import stacks_project.Chap73.Lemma_73_8_8_Site
public import stacks_project.Chap74.Lemma_74_10_2_BaseChange
public import stacks_project.Chap84.Lemma_84_5_2_Relocalization
public import stacks_project.Chap84.Lemma_84_6_4_Comparison
public import stacks_project.Chap84.Lemma_84_7_1_Sections
public import stacks_project.Chap84.Lemma_84_8_4_Comparison

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
instance spacesPullback_relocalization_isContinuous {X Y : AlgebraicSpace S} (f : Y ⟶ X) :
    (spacesEtalePullback f ⋙ Etale.SpacesToBig.relocalizationFunctor f).IsContinuous
      (spacesEtaleTopology X) (overEtaleTopology X) :=
  Functor.isContinuous_comp (spacesEtalePullback f)
    (Etale.SpacesToBig.relocalizationFunctor f)
    (spacesEtaleTopology X) (spacesEtaleTopology Y) (overEtaleTopology X)

/-- The pullback projection maps relocalized base changes to their original objects. -/
def pullbackRelocalizationToIdentity {X Y : AlgebraicSpace S} (f : Y ⟶ X) :
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

/-- Relocalization inverse image on type-valued sheaves. -/
def spacesInverseImage {X Y : AlgebraicSpace S} (f : Y ⟶ X) :
    Sheaf (overEtaleTopology X) (Type (u + 1)) ⥤
      Sheaf (spacesEtaleTopology Y) (Type (u + 1)) :=
  (Etale.SpacesToBig.relocalizationFunctor f).sheafPushforwardContinuous (Type (u + 1))
    (spacesEtaleTopology Y) (overEtaleTopology X)

/-- Restriction along identity-base spaces-étale relocalization. -/
def spacesIdPushforward (X : AlgebraicSpace S) :
    Sheaf (overEtaleTopology X) (Type (u + 1)) ⥤
      Sheaf (spacesEtaleTopology X) (Type (u + 1)) :=
  (Etale.SpacesToBig.relocalizationFunctor (𝟙 X)).sheafPushforwardContinuous (Type (u + 1))
    (spacesEtaleTopology X) (overEtaleTopology X)

/-- Inverse image along identity-base spaces-étale relocalization. -/
def spacesIdPullback (X : AlgebraicSpace S) :
    Sheaf (spacesEtaleTopology X) (Type (u + 1)) ⥤
      Sheaf (overEtaleTopology X) (Type (u + 1)) :=
  (Etale.SpacesToBig.relocalizationFunctor (𝟙 X)).sheafPullback (Type (u + 1))
    (spacesEtaleTopology X) (overEtaleTopology X)

/-- Restriction to the spaces étale site maps naturally to restriction after base change. -/
def restrictionComparison {X Y : AlgebraicSpace S} (f : Y ⟶ X) :
    spacesIdPushforward X ⟶
      spacesInverseImage f ⋙ (spacesEtaleMorphismOfTopoi f).pushforward :=
  sheafPushforwardContinuousNatTrans (pullbackRelocalizationToIdentity f) (Type (u + 1))
      (spacesEtaleTopology X) (overEtaleTopology X) ≫
    (sheafPushforwardContinuousComp (spacesEtalePullback f)
      (Etale.SpacesToBig.relocalizationFunctor f) (Type (u + 1))
      (spacesEtaleTopology X) (spacesEtaleTopology Y) (overEtaleTopology X)).inv

/-- Spaces-étale inverse image maps naturally to restriction of big-site inverse image. -/
def inverseImageComparison {X Y : AlgebraicSpace S} (f : Y ⟶ X) :
    (spacesEtaleMorphismOfTopoi f)⁻¹ ⟶
      spacesIdPullback X ⋙ spacesInverseImage f :=
  (((spacesEtaleMorphismOfTopoi f).adjunction.whiskerRight
    (Sheaf (spacesEtaleTopology X) (Type (u + 1)))).homEquiv
      (𝟭 _) (spacesIdPullback X ⋙ spacesInverseImage f)).symm
    (((Etale.SpacesToBig.relocalizationFunctor (𝟙 X)).sheafAdjunctionContinuous (Type (u + 1))
        (spacesEtaleTopology X) (overEtaleTopology X)).unit ≫
      whiskerLeft (spacesIdPullback X) (restrictionComparison f) ≫
      (associator (spacesIdPullback X) (spacesInverseImage f)
        (spacesEtaleMorphismOfTopoi f).pushforward).inv)

/-- Identity-base small-to-big relocalization is inclusion followed by spaces relocalization. -/
instance smallRelocalization_id_isContinuous (X : AlgebraicSpace S) :
    (smallEtaleInclusion X ⋙ Etale.SpacesToBig.relocalizationFunctor (𝟙 X)).IsContinuous
      (smallEtaleTopology X) (overEtaleTopology X) :=
  Functor.isContinuous_comp (smallEtaleInclusion X)
    (Etale.SpacesToBig.relocalizationFunctor (𝟙 X))
    (smallEtaleTopology X) (spacesEtaleTopology X) (overEtaleTopology X)

/-- Spaces identity pullback of `i_* F` maps to small-to-big inverse image of `F`. -/
def spacesIdPullbackToPiInverse {X : AlgebraicSpace S}
    (F : Sheaf (smallEtaleTopology X) (Type (u + 1))) :
    (spacesIdPullback X).obj
      ((smallEtaleInclusionInverseMorphismOfTopoi X).inverseImage.obj F) ⟶
      ((siteMorphismOfTopoi X)⁻¹).obj F :=
  let FX := (smallEtaleInclusionInverseMorphismOfTopoi X).inverseImage.obj F
  let πF := ((siteMorphismOfTopoi X)⁻¹).obj F
  let restrictComp :=
    sheafPushforwardContinuousComp (smallEtaleInclusion X)
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
        (restrictIso.inv.app ((spacesIdPushforward X).obj πF)) ≫
      (smallEtaleInclusionDirectImage X).asEquivalence.counitIso.hom.app
        ((spacesIdPushforward X).obj πF))

/-- Relocalization of the identity object of `Y_spaces,étale` is `Over.mk f`. -/
def relocalizationSelfIso {X Y : AlgebraicSpace S} (f : Y ⟶ X) :
    (Etale.SpacesToBig.relocalizationFunctor f).obj (spacesEtaleSite.self Y) ≅
      Over.mk f :=
  Over.isoMk (Iso.refl Y) rfl

/-- Global sections of `f_small⁻¹ F` map canonically to big-site inverse-image sections. -/
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
        ((smallEtaleInclusionDirectImage Y).asEquivalence.counitIso.app H).hom.hom s1
    let s3 :=
      (sectionsFunctor _).map ((inverseImageComparison f).app FX).hom s2
    let s4 :=
      sectionsEquivTerminal
        (((spacesInverseImage f).obj ((spacesIdPullback X).obj FX)).obj)
        (spacesEtaleSite.self Y) (isTerminal_self Y) s3
    (spacesIdPullbackToPiInverse F).hom.app (op (Over.mk f))
      (((spacesIdPullback X).obj FX).1.map (relocalizationSelfIso f).inv.op
        ((Etale.SpacesToBig.inverseImage_objObjIso f ((spacesIdPullback X).obj FX)
            (spacesEtaleSite.self Y)).hom s4))

/-- `sectionsComparison` is assembled from spaces-étale inverse-image comparison,
terminal evaluation, and relocalization of `spacesEtaleSite.self Y`. -/
theorem sectionsComparison_eq {X Y : AlgebraicSpace S} (f : Y ⟶ X)
    (F : Sheaf (smallEtaleTopology X) (Type (u + 1))) :
    sectionsComparison f F = fun sectionValue ↦
      let FX := (smallEtaleInclusionInverseMorphismOfTopoi X).inverseImage.obj F
      let H := (spacesEtaleMorphismOfTopoi f).inverseImage.obj FX
      let G := (smallEtaleMorphismOfTopoi f).inverseImage.obj F
      let s1 :=
        ((smallEtaleInclusionMorphismOfTopoi Y).pushforwardSectionsEquiv G).symm sectionValue
      let s2 :=
        (sectionsFunctor _).map
          ((smallEtaleInclusionDirectImage Y).asEquivalence.counitIso.app H).hom.hom s1
      let s3 :=
        (sectionsFunctor _).map ((inverseImageComparison f).app FX).hom s2
      let s4 :=
        sectionsEquivTerminal
          (((spacesInverseImage f).obj ((spacesIdPullback X).obj FX)).obj)
          (spacesEtaleSite.self Y) (isTerminal_self Y) s3
      (spacesIdPullbackToPiInverse F).hom.app (op (Over.mk f))
        (((spacesIdPullback X).obj FX).1.map (relocalizationSelfIso f).inv.op
          ((Etale.SpacesToBig.inverseImage_objObjIso f ((spacesIdPullback X).obj FX)
              (spacesEtaleSite.self Y)).hom s4)) :=
  rfl

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
    Presheaf.IsSheaf (overFpqcTopology X)
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
