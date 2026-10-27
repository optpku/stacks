/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Presheaf.ChangeOfRings.Adjunction

/-!
# Pullback of module presheaves at the size of the indexing categories
-/

public section
open CategoryTheory Opposite
noncomputable section
universe u v

namespace PresheafOfModules.SiteSized

variable {C D : Type u} [Category.{v} C] [Category.{v} D]

/-- Raise objects and arrows to one common indexing universe using explicit lifts. -/
private def reindexFunctor (F : C ⥤ D) : AsSmall.{0} C ⥤ AsSmall.{0} D :=
  AsSmall.down ⋙ F ⋙ AsSmall.up

/-- The reindexed coefficient map consists of the original component maps. -/
private def reindexCoefficients {F : C ⥤ D} {S : Cᵒᵖ ⥤ RingCat.{max u v}}
    {R : Dᵒᵖ ⥤ RingCat.{max u v}} (φ : S ⟶ F.op ⋙ R) :
    (AsSmall.down : AsSmall.{0} C ⥤ C).op ⋙ S ⟶
      (reindexFunctor F).op ⋙ (AsSmall.down : AsSmall.{0} D ⥤ D).op ⋙ R :=
  Functor.whiskerLeft AsSmall.down.op φ

/-- Extension of module presheaves through the canonical small presentations
of the indexing categories, preserving the universe of section carriers. -/
def pullback {F : C ⥤ D} {S : Cᵒᵖ ⥤ RingCat.{max u v}}
    {R : Dᵒᵖ ⥤ RingCat.{max u v}} (φ : S ⟶ F.op ⋙ R) :
    PresheafOfModules.{max u v} S ⥤ PresheafOfModules.{max u v} R := by
  exact PresheafOfModules.pushforward₀ (AsSmall.down : AsSmall.{0} C ⥤ C) S ⋙
    PresheafOfModules.pullback (reindexCoefficients φ) ⋙
      PresheafOfModules.pushforward₀ (AsSmall.up : D ⥤ AsSmall.{0} D)
        ((AsSmall.down : AsSmall.{0} D ⥤ D).op ⋙ R)

/-- The explicit extension is genuinely left adjoint to the original
restriction functor, with the adjunction constructed from the specified pair. -/
def pullbackPushforwardAdjunction {F : C ⥤ D} {S : Cᵒᵖ ⥤ RingCat.{max u v}}
    {R : Dᵒᵖ ⥤ RingCat.{max u v}} (φ : S ⟶ F.op ⋙ R) :
    pullback φ ⊣ PresheafOfModules.pushforward φ := by
  exact (((ChangeOfRings.asSmallEquivalence S).toAdjunction.comp
    (PresheafOfModules.pullbackPushforwardAdjunction (reindexCoefficients φ))).comp
      (ChangeOfRings.asSmallEquivalence R).symm.toAdjunction).ofNatIsoRight (Iso.refl _)

/-- Pushforward of module presheaves is right adjoint to site-sized pullback. -/
instance pushforwardIsRightAdjoint {F : C ⥤ D} {S : Cᵒᵖ ⥤ RingCat.{max u v}}
    {R : Dᵒᵖ ⥤ RingCat.{max u v}} (φ : S ⟶ F.op ⋙ R) :
    (PresheafOfModules.pushforward.{max u v} φ).IsRightAdjoint :=
  (pullbackPushforwardAdjunction φ).isRightAdjoint

end PresheafOfModules.SiteSized
