module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous.Restrict
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.Restriction

/-!
# Pullback across an isomorphism of target ring sheaves

This file identifies pullback along an isomorphic target ring sheaf with pullback followed by
restriction of scalars.  The comparison is characterized canonically by uniqueness of left
adjoints.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u v w z u' v'

namespace SheafOfModules

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
variable {J : GrothendieckTopology C} {K : GrothendieckTopology D}
variable {F : C ⥤ D} [F.IsContinuous J K]
variable {S : Sheaf J RingCat.{w}} {R R' : Sheaf K RingCat.{w}}

/-- Pullback along an isomorphic target ring sheaf is canonically pullback followed by
restriction of scalars along the inverse isomorphism. -/
noncomputable def pullbackIsoOfIso
    (φ : S ⟶ (F.sheafPushforwardContinuous RingCat.{w} J K).obj R)
    (φ' : S ⟶ (F.sheafPushforwardContinuous RingCat.{w} J K).obj R')
    (e : R ≅ R')
    (h : φ ≫ (F.sheafPushforwardContinuous RingCat.{w} J K).map e.hom = φ')
    [(pushforward.{z} φ).IsRightAdjoint]
    [(pushforward.{z} φ').IsRightAdjoint] :
    pullback.{z} φ' ≅ pullback.{z} φ ⋙ restrictScalars.{z} e.inv :=
  Adjunction.leftAdjointUniq (pullbackPushforwardAdjunction φ')
    (((pullbackPushforwardAdjunction φ).comp
      (Restriction.equivalenceOfIso e).toAdjunction).ofNatIsoRight
        (restrictPushforwardIso e.hom φ φ' h))

end SheafOfModules
