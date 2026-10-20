/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RepresentationTheory.CompletedGroupRing.Basic

@[expose] public section
open CategoryTheory
open scoped MonoidAlgebra
noncomputable section
universe r v w m

namespace completedGroupRing
variable (Λ : Type r) [Ring Λ]
variable {G : Type v} {H : Type w}
variable [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
variable (e : G ≃* H) (he : Continuous e)

/-- The actual induced map on the corresponding group quotients. -/
def quotientMap (N : OpenNormalSubgroup H) :
    G ⧸ (N.comap e.toMonoidHom he).toSubgroup →* H ⧸ N.toSubgroup :=
  QuotientGroup.map (N.comap e.toMonoidHom he).toSubgroup N.toSubgroup e.toMonoidHom
    (by intro x hx; exact hx)

/-- Map the actual finite-stage group-algebra coefficients along the quotient map. -/
def stageMap (N : OpenNormalSubgroup H) :
    MonoidAlgebra Λ (G ⧸ (N.comap e.toMonoidHom he).toSubgroup) →+*
      MonoidAlgebra Λ (H ⧸ N.toSubgroup) :=
  MonoidAlgebra.mapDomainRingHom Λ (quotientMap e he N)

theorem compatible (x : completedGroupRing Λ G) :
    CompletedGroupRing.IsCompatible Λ H
      (fun N ↦ stageMap Λ e he N (x.val (N.comap e.toMonoidHom he))) := sorry

/-- The completed-ring map is specified at every open-normal quotient. -/
def hom : completedGroupRing Λ G →+* completedGroupRing Λ H where
  toFun x :=
    ⟨fun N ↦ stageMap Λ e he N (x.val (N.comap e.toMonoidHom he)), compatible Λ e he x⟩
  map_zero' := sorry
  map_one' := sorry
  map_add' := sorry
  map_mul' := sorry

variable (heinv : Continuous e.symm)

/-- The inverse also uses the actual inverse continuous equivalence on all
finite-stage projections. Mixed group/coefficient universes are retained. -/
def ringEquiv : completedGroupRing Λ G ≃+* completedGroupRing Λ H where
  toFun := hom Λ e he
  invFun := hom Λ e.symm heinv
  left_inv := sorry
  right_inv := sorry
  map_add' := (hom Λ e he).map_add
  map_mul' := (hom Λ e he).map_mul

theorem projection (x : completedGroupRing Λ G) (N : OpenNormalSubgroup H) :
    (ringEquiv Λ e he heinv x).val N = stageMap Λ e he N (x.val (N.comap e.toMonoidHom he)) := rfl

/-- Scalar transport preserves the underlying module and its maps. -/
def restrictScalars : ModuleCat.{m} (completedGroupRing Λ G) ⥤ ModuleCat.{m} (completedGroupRing Λ H) :=
  ModuleCat.restrictScalars (ringEquiv Λ e he heinv).symm.toRingHom

/-- Restriction through the specified completed-ring equivalence is additive. -/
instance restrictScalars_additive : (restrictScalars Λ e he heinv).Additive :=
  inferInstanceAs
    ((ModuleCat.restrictScalars (ringEquiv Λ e he heinv).symm.toRingHom).Additive)

end completedGroupRing
