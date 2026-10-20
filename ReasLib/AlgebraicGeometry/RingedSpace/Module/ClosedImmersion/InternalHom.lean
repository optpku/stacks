/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Adjunction.Restrict
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.InternalHom
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous.Restrict
public import ReasLib.Algebra.Category.Ring.Sheaf.LocallySurjective
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.ClosedImmersion.Pushforward

@[expose] public section

open CategoryTheory Opposite
open AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace.Hom.ModulePushforward.ClosedImmersion

variable {X Z : RingedSpace.{u}} (i : Z ⟶ X)

/-- The direct image of `𝒪_Z` as a commutative ring sheaf on `X`. -/
noncomputable abbrev pushedStructureSheaf :=
  (TopCat.Sheaf.pushforward CommRingCat i.hom.base).obj Z.sheaf

/-- Direct image before restriction of scalars along `𝒪_X ⟶ i_*𝒪_Z`. -/
noncomputable def pushforwardOverStructureSheaf :
    Z.Modules ⥤ SheafOfModules.RingedSite.ringedSiteModuleCategory
      (Opens.grothendieckTopology X) (pushedStructureSheaf i) :=
  SheafOfModules.pushforward
    (F := TopologicalSpace.Opens.map i.hom.base)
    (TopCat.Sheaf.ringSheafOfCommMap (𝟙 (pushedStructureSheaf i)))

/-- Restricting scalars after direct image over `i_*𝒪_Z` recovers module pushforward. -/
noncomputable def pushforwardFactorIso :
    pushforwardOverStructureSheaf i ⋙
        SheafOfModules.RingedSite.restrictionAlong.{u, u, u, u}
          (RingedSpace.Hom.commRingSheafPushforwardMap i) ≅
      RingedSpace.Hom.pushforward i :=
  SheafOfModules.pushforwardRestrictIso
    (F := TopologicalSpace.Opens.map i.hom.base)
    (R := Z.ringCatSheaf)
    (TopCat.Sheaf.ringSheafOfCommMap
      (RingedSpace.Hom.commRingSheafPushforwardMap i))
    (TopCat.Sheaf.ringSheafOfCommMap (𝟙 (pushedStructureSheaf i)))

/-- The ambient internal-Hom functor from the pushed-forward structure sheaf of `Z`. -/
noncomputable abbrev ambientInternalHom
    [Sheaf.IsLocallySurjective (RingedSpace.Hom.commRingSheafPushforwardMap i)] :
    X.Modules ⥤ X.Modules :=
  SheafOfModules.RingedSite.coextendAlong.{u, u, u}
      (RingedSpace.Hom.commRingSheafPushforwardMap i) ⋙
    SheafOfModules.RingedSite.restrictionAlong.{u, u, u, u}
      (RingedSpace.Hom.commRingSheafPushforwardMap i)

/-- Restriction along `𝒪_X ⟶ i_*𝒪_Z` is fully faithful under the local-surjectivity
hypothesis. -/
noncomputable def scalarRestrictionFullyFaithful
    [Sheaf.IsLocallySurjective (RingedSpace.Hom.commRingSheafPushforwardMap i)] :
    (SheafOfModules.RingedSite.restrictionAlong.{u, u, u, u}
      (RingedSpace.Hom.commRingSheafPushforwardMap i)).FullyFaithful :=
  SheafOfModules.restrictScalarsFullyFaithfulOfIsLocallySurjective
    (TopCat.Sheaf.ringSheafOfCommMap
      (RingedSpace.Hom.commRingSheafPushforwardMap i))

/-- The ambient internal Hom from `i_*𝒪_Z` belongs to the essential image of module
pushforward along the closed immersion. -/
theorem ambientInternalHom_mem_essImage
    (h_closed : Topology.IsClosedEmbedding i.hom.base)
    [Sheaf.IsLocallySurjective (RingedSpace.Hom.commRingSheafPushforwardMap i)]
    (F : X.Modules) :
    (RingedSpace.Hom.pushforward i).essImage ((ambientInternalHom i).obj F) := sorry

/-- The ambient internal-Hom functor, valued in the essential image of closed-immersion
pushforward. -/
noncomputable def ambientInternalHomToEssImage
    (h_closed : Topology.IsClosedEmbedding i.hom.base)
    [Sheaf.IsLocallySurjective (RingedSpace.Hom.commRingSheafPushforwardMap i)] :
    X.Modules ⥤ (RingedSpace.Hom.pushforward i).EssImageSubcategory :=
  (RingedSpace.Hom.pushforward i).essImage.lift (ambientInternalHom i)
    (ambientInternalHom_mem_essImage i h_closed)

/-- Pushforward along the closed immersion, regarded as an equivalence with its essential
image under the minimal closed-embedding and local-surjectivity hypotheses. -/
noncomputable def pushforwardEssImageEquivalence
    (h_closed : Topology.IsClosedEmbedding i.hom.base)
    [Sheaf.IsLocallySurjective (RingedSpace.Hom.commRingSheafPushforwardMap i)] :
    Z.Modules ≌ (RingedSpace.Hom.pushforward i).EssImageSubcategory :=
  -- Local instance justification (proof-local temporary data): the essential-image equivalence consumes the explicit fully faithful datum for this fixed closed embedding.
  letI : (RingedSpace.Hom.pushforward i).Full :=
    (fullyFaithful i h_closed).full
  -- Local instance justification (proof-local temporary data): the essential-image equivalence consumes the explicit fully faithful datum for this fixed closed embedding.
  letI : (RingedSpace.Hom.pushforward i).Faithful :=
    (fullyFaithful i h_closed).faithful
  (RingedSpace.Hom.pushforward i).toEssImage.asEquivalence

/-- The closed-immersion internal-Hom functor, obtained by transporting the explicit ambient
internal Hom from `i_*𝒪_Z` back through the pushforward essential-image equivalence. -/
noncomputable def homFromStructureSheaf
    (h_closed : Topology.IsClosedEmbedding i.hom.base)
    [Sheaf.IsLocallySurjective (RingedSpace.Hom.commRingSheafPushforwardMap i)] :
    X.Modules ⥤ Z.Modules :=
  ambientInternalHomToEssImage i h_closed ⋙
    (pushforwardEssImageEquivalence i h_closed).inverse

/-- Pushing forward the transported internal Hom recovers the explicit ambient internal Hom
from `i_*𝒪_Z`. -/
noncomputable def pushforwardHomFromStructureSheafIso
    (h_closed : Topology.IsClosedEmbedding i.hom.base)
    [Sheaf.IsLocallySurjective (RingedSpace.Hom.commRingSheafPushforwardMap i)] :
    homFromStructureSheaf i h_closed ⋙ RingedSpace.Hom.pushforward i ≅
      ambientInternalHom i :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (ambientInternalHomToEssImage i h_closed)
      ((Functor.isoWhiskerLeft (pushforwardEssImageEquivalence i h_closed).inverse
        (Functor.toEssImageCompι (RingedSpace.Hom.pushforward i))).symm ≪≫
        (Functor.associator _ _ _).symm ≪≫
        Functor.isoWhiskerRight
          (pushforwardEssImageEquivalence i h_closed).counitIso
          (RingedSpace.Hom.pushforward i).essImage.ι ≪≫
        (RingedSpace.Hom.pushforward i).essImage.ι.leftUnitor) ≪≫
    (RingedSpace.Hom.pushforward i).essImage.liftCompιIso
      (ambientInternalHom i) (ambientInternalHom_mem_essImage i h_closed)

/-- The adjunction between closed-immersion pushforward and the transported internal-Hom
functor. -/
noncomputable def adjunction
    (h_closed : Topology.IsClosedEmbedding i.hom.base)
    [Sheaf.IsLocallySurjective (RingedSpace.Hom.commRingSheafPushforwardMap i)] :
    RingedSpace.Hom.pushforward i ⊣ homFromStructureSheaf i h_closed :=
  -- Local instance justification (proof-local temporary data): cancellation through scalar restriction consumes the explicit full-faithfulness datum for this fixed ring-sheaf map.
  letI : (SheafOfModules.RingedSite.restrictionAlong.{u, u, u, u}
      (RingedSpace.Hom.commRingSheafPushforwardMap i)).Full :=
    (scalarRestrictionFullyFaithful i).full
  -- Local instance justification (proof-local temporary data): both cancellation and recovery of full faithfulness consume the same explicit datum for this fixed ring-sheaf map.
  letI : (SheafOfModules.RingedSite.restrictionAlong.{u, u, u, u}
      (RingedSpace.Hom.commRingSheafPushforwardMap i)).Faithful :=
    (scalarRestrictionFullyFaithful i).faithful
  let pushforwardOverStructureSheafFullyFaithful :
      (pushforwardOverStructureSheaf i).FullyFaithful :=
    Functor.FullyFaithful.ofCompFaithful
      ((fullyFaithful i h_closed).ofIso (pushforwardFactorIso i).symm)
  let rightComparison :
      homFromStructureSheaf i h_closed ⋙ pushforwardOverStructureSheaf i ≅
        SheafOfModules.RingedSite.coextendAlong.{u, u, u}
          (RingedSpace.Hom.commRingSheafPushforwardMap i) :=
    Functor.fullyFaithfulCancelRight
      (SheafOfModules.RingedSite.restrictionAlong.{u, u, u, u}
        (RingedSpace.Hom.commRingSheafPushforwardMap i))
      (Functor.associator _ _ _ ≪≫
        Functor.isoWhiskerLeft (homFromStructureSheaf i h_closed)
          (pushforwardFactorIso i) ≪≫
        pushforwardHomFromStructureSheafIso i h_closed)
  (SheafOfModules.RingedSite.restrictionCoextendAdj
      (RingedSpace.Hom.commRingSheafPushforwardMap i)).restrictFullyFaithful
    pushforwardOverStructureSheafFullyFaithful (Functor.FullyFaithful.id _)
    (pushforwardFactorIso i ≪≫ (RingedSpace.Hom.pushforward i).rightUnitor.symm)
    ((SheafOfModules.RingedSite.coextendAlong.{u, u, u}
      (RingedSpace.Hom.commRingSheafPushforwardMap i)).leftUnitor ≪≫ rightComparison.symm)

/-- The counit of the pushforward/internal-Hom adjunction is bijective from all sections
over the inverse-image open onto the ambient sections annihilated by the ideal sheaf. -/
theorem homFromStructureSheaf_sections_bijOn
    (h_closed : Topology.IsClosedEmbedding i.hom.base)
    [Sheaf.IsLocallySurjective (RingedSpace.Hom.commRingSheafPushforwardMap i)]
    (𝒥 : X.Modules) (U : TopologicalSpace.Opens X.carrier) :
    Set.BijOn
      (((adjunction i h_closed).counit.app 𝒥).val.app (op U))
      Set.univ
      {s | ∀ r : (RingedSpace.Hom.idealSheaf i).val.obj (op U),
        ((RingedSpace.Hom.idealSheafι i).val.app (op U) r) • s = 0} := sorry

end AlgebraicGeometry.RingedSpace.Hom.ModulePushforward.ClosedImmersion
