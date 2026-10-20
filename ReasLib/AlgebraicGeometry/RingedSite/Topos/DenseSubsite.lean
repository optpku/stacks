/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.Topos.Hom
public import ReasLib.CategoryTheory.Sites.DenseSubsite.Ring
public import ReasLib.CategoryTheory.Sites.DenseSubsite.Topos

/-!
# Ringed topoi from dense subsites

A ring sheaf on a site restricts to a dense subsite.  The dense-subsite
equivalence and its counit then give the canonical comparison from the
restricted ringed topos to the original ringed topos.
-/

@[expose] public section

open CategoryTheory Limits

noncomputable section

universe u₁ u₂ v₁ v₂ w

namespace RingedSite.DenseSubsite

variable {C : Type u₁} [Category.{v₁} C]
variable {D : Type u₂} [Category.{v₂} D]
variable (G : C ⥤ D) (J : GrothendieckTopology C) (K : GrothendieckTopology D)
variable [G.IsDenseSubsite J K]
variable [∀ X, HasLimitsOfShape (StructuredArrow X G.op) RingCat.{w}]
variable [∀ X, HasLimitsOfShape (StructuredArrow X G.op) (Type w)]
variable [J.HasSheafCompose (forget RingCat.{w})]
variable [K.HasSheafCompose (forget RingCat.{w})]

/-- The restriction of a ring-valued sheaf to a dense subsite. -/
noncomputable def restrictedStructureSheaf (O : Sheaf K RingCat.{w}) :
    Sheaf J RingCat.{w} :=
  (G.sheafPushforwardContinuous RingCat.{w} J K).obj O

/-- A dense subsite equipped with the restriction of a ring sheaf from the ambient site. -/
noncomputable abbrev restrictedRingedSite (O : Sheaf K RingCat.{w}) :
    RingedSite.{u₁, v₁, w} :=
  RingedSite.ofRingSheaf J (restrictedStructureSheaf G J K O)

/-- The counit map from an ambient ring sheaf to the dense-subsite transport of its
restriction. -/
noncomputable def structureMap (O : Sheaf K RingCat.{w}) :
    O ⟶ (Functor.IsDenseSubsite.ringTransport G J K).obj
      (restrictedStructureSheaf G J K O) :=
  (Functor.IsDenseSubsite.sheafEquiv J K G RingCat.{w}).counitIso.inv.app O

/-- The counit presentation of the dense-subsite structure map preserves the ring
operations after passage to underlying sheaves. -/
theorem structureMap_isRingCompatible (O : Sheaf K RingCat.{w}) :
    ToposHom.Direct.IsRingCompatible
      (X := restrictedRingedSite G J K O) (Y := RingedSite.ofRingSheaf K O)
      (Functor.IsDenseSubsite.morphismOfTopoiIn G)
      (Functor.IsDenseSubsite.ringTransport G J K)
      (Functor.IsDenseSubsite.ringTransportForgetIso G J K)
      (structureMap G J K O) := sorry

/-- The canonical morphism from a dense subsite with its restricted ring sheaf to the
ambient ringed topos. -/
noncomputable def comparison (O : Sheaf K RingCat.{w}) :
    ToposHom (restrictedRingedSite G J K O) (RingedSite.ofRingSheaf K O) :=
  ToposHom.ofDirectImage
    (Functor.IsDenseSubsite.morphismOfTopoiIn G)
    (Functor.IsDenseSubsite.ringTransport G J K)
    (Functor.IsDenseSubsite.ringTransportForgetIso G J K)
    (structureMap G J K O) (structureMap_isRingCompatible G J K O)

end RingedSite.DenseSubsite
