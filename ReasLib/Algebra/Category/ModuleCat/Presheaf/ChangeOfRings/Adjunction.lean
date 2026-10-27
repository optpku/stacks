/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Pullback
public import Mathlib.CategoryTheory.Category.ULift

public section

open CategoryTheory CategoryTheory.Functor

universe u v

noncomputable section

namespace PresheafOfModules.ChangeOfRings

variable {C : Type u} [Category.{v} C]
variable (R : Cᵒᵖ ⥤ RingCat.{max u v})

/-- Module presheaves are equivalent to their reindexing on the canonical small category. -/
@[expose]
def asSmallEquivalence :
    PresheafOfModules.{max u v} R ≌
      PresheafOfModules.{max u v} (AsSmall.down.op ⋙ R) where
  functor := pushforward₀ (AsSmall.down : AsSmall.{0} C ⥤ C) R
  inverse := pushforward₀ AsSmall.up (AsSmall.down.op ⋙ R)
  unitIso := Iso.refl _
  counitIso := Iso.refl _

variable {R} {R' : Cᵒᵖ ⥤ RingCat.{max u v}} (α : R ⟶ R')

/-- Extension of scalars on a possibly large indexing category, transported from its
canonical small-category presentation. -/
def extendScalars : PresheafOfModules.{max u v} R ⥤ PresheafOfModules.{max u v} R' :=
  ((asSmallEquivalence R).functor ⋙
    pullback (F := 𝟭 (AsSmall.{0} C))
      (R := (AsSmall.down : AsSmall.{0} C ⥤ C).op ⋙ R')
      (whiskerLeft (AsSmall.down : AsSmall.{0} C ⥤ C).op α)) ⋙
      (asSmallEquivalence R').inverse

/-- Extension and restriction of scalars on module presheaves form an adjunction. -/
def extendRestrictAdjunction : extendScalars α ⊣ restrictScalars α :=
  (((asSmallEquivalence R).toAdjunction.comp
    (pullbackPushforwardAdjunction (F := 𝟭 (AsSmall.{0} C))
      (R := (AsSmall.down : AsSmall.{0} C ⥤ C).op ⋙ R')
      (whiskerLeft (AsSmall.down : AsSmall.{0} C ⥤ C).op α))).comp
        (asSmallEquivalence R').symm.toAdjunction).ofNatIsoRight
          (Iso.refl _)

/-- Restriction of scalars on module presheaves is a right adjoint. -/
instance restrictScalarsIsRightAdjoint : (restrictScalars.{max u v} α).IsRightAdjoint :=
  ⟨⟨extendScalars α, ⟨extendRestrictAdjunction α⟩⟩⟩

/-- Identity-site pushforward along a coefficient morphism is a right adjoint. -/
instance pushforwardOverIdIsRightAdjoint :
    (pushforward.{max u v} (F := 𝟭 C) α).IsRightAdjoint :=
  Functor.isRightAdjoint_of_iso (Iso.refl (restrictScalars.{max u v} α))

end PresheafOfModules.ChangeOfRings
