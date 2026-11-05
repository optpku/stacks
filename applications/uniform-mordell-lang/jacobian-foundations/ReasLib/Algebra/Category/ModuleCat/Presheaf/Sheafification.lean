module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.Topology.Sheaves.CommRingCat
public import ReasLib.Algebra.Category.ModuleCat.Presheaf.CommRing
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Sheafification of commutative-ring module presheaves

This leaf owns the comparison between sheafification before and after forgetting
commutativity, together with the induced module-sheafification functor.
-/

@[expose] public section

open CategoryTheory
open SheafOfModules.RingedSite (ringSheaf ringedSiteModuleCategory)

noncomputable section

universe u v w z

namespace PresheafOfModules

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
variable [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
variable [HasWeakSheafify J CommRingCat.{w}]

/-- The commutative-ring-valued sheafification of a presheaf of commutative rings. -/
abbrev commRingSheafification (𝒪 : Cᵒᵖ ⥤ CommRingCat.{w}) :
    Sheaf J CommRingCat.{w} :=
  (presheafToSheaf J CommRingCat.{w}).obj 𝒪

/-- The map on commutative ring sheafifications induced by a presheaf morphism. -/
abbrev commRingSheafificationMap {𝒪 𝒪' : Cᵒᵖ ⥤ CommRingCat.{w}}
    (α : 𝒪 ⟶ 𝒪') :
    commRingSheafification J 𝒪 ⟶ commRingSheafification J 𝒪' :=
  (presheafToSheaf J CommRingCat.{w}).map α

/-- The canonical ring map from a commutative-ring-valued presheaf to the underlying ring
presheaf of its sheafification. -/
abbrev sheafificationRingMap (𝒪 : Cᵒᵖ ⥤ CommRingCat.{w}) :
    ringPresheaf 𝒪 ⟶ (ringSheaf J (commRingSheafification J 𝒪)).obj :=
  presheafStructureMap (CategoryTheory.toSheafify J 𝒪)

/-- The underlying ring sheafification map is the commutative-ring sheafification unit after
forgetting commutativity. -/
theorem sheafificationRingMap_eq_whiskerRight
    (𝒪 : Cᵒᵖ ⥤ CommRingCat.{w}) :
    sheafificationRingMap J 𝒪 =
      Functor.whiskerRight (CategoryTheory.toSheafify J 𝒪)
        (forget₂ CommRingCat RingCat) := sorry

/-- On every object of the site, `sheafificationRingMap` is the ring homomorphism underlying the
commutative-ring sheafification unit. -/
@[simp]
theorem sheafificationRingMap_app_hom
    (𝒪 : Cᵒᵖ ⥤ CommRingCat.{w}) (X : Cᵒᵖ) :
    ((sheafificationRingMap J 𝒪).app X).hom =
      ((CategoryTheory.toSheafify J 𝒪).app X).hom := sorry

/-- The ring sheafification map is natural in a morphism of commutative-ring presheaves. -/
theorem sheafificationRingMap_naturality {𝒪 𝒪' : Cᵒᵖ ⥤ CommRingCat.{w}}
    (α : 𝒪 ⟶ 𝒪') :
    presheafStructureMap α ≫ sheafificationRingMap J 𝒪' =
      sheafificationRingMap J 𝒪 ≫
        (sheafToPresheaf J RingCat.{w}).map
          (SheafOfModules.RingedSite.ringSheafMap
            (commRingSheafificationMap J α)) := sorry

/-- Naturality of commutative-ring sheafification as a square of ring-presheaf data. -/
@[stacks 08TP "commutative-ring sheafification square",
  stacks 0G3U "commutative-ring sheafification square"]
theorem commRingSheafificationSquare {𝒪 𝒪' : Cᵒᵖ ⥤ CommRingCat.{w}}
    (α : 𝒪 ⟶ 𝒪') :
    CommSq (CategoryTheory.toSheafify J 𝒪) α
      (commRingSheafificationMap J α).hom
      (CategoryTheory.toSheafify J 𝒪') := sorry

/-- The canonical ring sheafification map is locally injective. -/
instance sheafificationRingMap_isLocallyInjective
    [J.WEqualsLocallyBijective CommRingCat.{w}]
    (𝒪 : Cᵒᵖ ⥤ CommRingCat.{w}) :
    Presheaf.IsLocallyInjective J (sheafificationRingMap J 𝒪) := sorry

/-- The canonical ring sheafification map is locally surjective. -/
instance sheafificationRingMap_isLocallySurjective
    [J.WEqualsLocallyBijective CommRingCat.{w}]
    (𝒪 : Cᵒᵖ ⥤ CommRingCat.{w}) :
    Presheaf.IsLocallySurjective J (sheafificationRingMap J 𝒪) := sorry

/-- Sheafification of presheaves of modules along the canonical map from a commutative-ring
presheaf to its sheafification.

The local injectivity and surjectivity witnesses are explicit inferable inputs so the functor's
computational data does not capture a particular proof implementation. -/
abbrev moduleSheafification (𝒪 : Cᵒᵖ ⥤ CommRingCat.{w})
    [HasWeakSheafify J AddCommGrpCat.{z}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{z}]
    [Presheaf.IsLocallyInjective J (sheafificationRingMap J 𝒪)]
    [Presheaf.IsLocallySurjective J (sheafificationRingMap J 𝒪)] :
    PresheafOfModules.{z} (ringPresheaf 𝒪) ⥤
      ringedSiteModuleCategory.{u, v, z, w} J (commRingSheafification J 𝒪) :=
  PresheafOfModules.sheafification.{z} (sheafificationRingMap J 𝒪)

end PresheafOfModules
