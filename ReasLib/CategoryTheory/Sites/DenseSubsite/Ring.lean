/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.CategoryTheory.Sites.DenseSubsite.SheafEquiv
import Mathlib.Tactic.CrossRefAttribute

/-!
# Ring-valued sheaves on a dense subsite

The comparison equivalence for a dense subsite canonically transports ring-valued sheaves to
the larger site.  This module records that specialization independently of any ringed-space or
ringed-topos presentation.
-/

@[expose] public section

open CategoryTheory Limits

noncomputable section

universe u₁ u₂ v₁ v₂ w

namespace CategoryTheory.Functor.IsDenseSubsite

variable {C : Type u₁} [Category.{v₁} C]
variable {D : Type u₂} [Category.{v₂} D]

/-- The canonical transport of a ring-valued sheaf from a dense subsite to the larger site. -/
@[stacks 03CR "ring transport"]
noncomputable abbrev ringTransport
    (G : C ⥤ D) (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    [G.IsDenseSubsite J K]
    [∀ X, HasLimitsOfShape (StructuredArrow X G.op) RingCat.{w}] :
    Sheaf J RingCat.{w} ⥤ Sheaf K RingCat.{w} :=
  (sheafEquiv J K G RingCat.{w}).functor

/-- Continuous pushforward of the canonical dense-subsite ring transport recovers the original
ring-valued sheaf. -/
noncomputable abbrev ringTransportIso
    (G : C ⥤ D) (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    [G.IsDenseSubsite J K]
    [∀ X, HasLimitsOfShape (StructuredArrow X G.op) RingCat.{w}]
    (O : Sheaf J RingCat.{w}) :
    (G.sheafPushforwardContinuous RingCat.{w} J K).obj
        ((ringTransport G J K).obj O) ≅ O :=
  ((sheafEquiv J K G RingCat.{w}).unitIso.app O).symm

/-- Restriction along a dense-subsite functor commutes canonically with forgetting a ring-valued
sheaf to its underlying type-valued sheaf. -/
noncomputable def ringRestrictionForgetIso
    (G : C ⥤ D) (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    [G.IsDenseSubsite J K]
    [∀ X, HasLimitsOfShape (StructuredArrow X G.op) RingCat.{w}]
    [∀ X, HasLimitsOfShape (StructuredArrow X G.op) (Type w)]
    [J.HasSheafCompose (forget RingCat.{w})]
    [K.HasSheafCompose (forget RingCat.{w})] :
    (sheafEquiv J K G RingCat.{w}).inverse ⋙
        sheafCompose J (forget RingCat.{w}) ≅
      sheafCompose K (forget RingCat.{w}) ⋙
        (sheafEquiv J K G (Type w)).inverse :=
  Iso.refl _

/-- Transporting a ring-valued sheaf across a dense subsite and then forgetting its ring
structure agrees canonically with transporting its underlying type-valued sheaf. -/
@[stacks 03CR "ring transport forgetful comparison"]
noncomputable def ringTransportForgetIso
    (G : C ⥤ D) (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    [G.IsDenseSubsite J K]
    [∀ X, HasLimitsOfShape (StructuredArrow X G.op) RingCat.{w}]
    [∀ X, HasLimitsOfShape (StructuredArrow X G.op) (Type w)]
    [J.HasSheafCompose (forget RingCat.{w})]
    [K.HasSheafCompose (forget RingCat.{w})] :
    ringTransport G J K ⋙ sheafCompose K (forget RingCat.{w}) ≅
      sheafCompose J (forget RingCat.{w}) ⋙
        (sheafEquiv J K G (Type w)).functor :=
  ((Functor.whiskeringLeft
    (Sheaf K RingCat.{w}) (Sheaf J RingCat.{w}) (Sheaf K (Type w))).obj
      (sheafEquiv J K G RingCat.{w}).inverse).preimageIso
        (((Functor.associator _ _ _).symm ≪≫
            Functor.isoWhiskerRight (sheafEquiv J K G RingCat.{w}).counitIso _ ≪≫
            Functor.leftUnitor _) ≪≫
          (((Functor.associator _ _ _).symm ≪≫
            Functor.isoWhiskerRight (ringRestrictionForgetIso G J K)
              (sheafEquiv J K G (Type w)).functor ≪≫
            Functor.associator _ _ _ ≪≫
            Functor.isoWhiskerLeft (sheafCompose K (forget RingCat.{w}))
              (sheafEquiv J K G (Type w)).counitIso ≪≫
            Functor.rightUnitor _).symm))

-- The transport data and its coefficient comparisons come from mathlib's canonical
-- dense-subsite equivalences.

end CategoryTheory.Functor.IsDenseSubsite
