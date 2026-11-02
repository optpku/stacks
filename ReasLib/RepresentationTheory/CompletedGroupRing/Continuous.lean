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
      (fun N ↦ stageMap Λ e he N (x.val (N.comap e.toMonoidHom he))) := by
  intro N N' h
  have hc := OpenNormalSubgroup.comap_mono e.toMonoidHom he h
  have hsquare :
      (CompletedGroupRing.transition Λ H h).comp (stageMap Λ e he N) =
        (stageMap Λ e he N').comp (CompletedGroupRing.transition Λ G hc) := by
    unfold CompletedGroupRing.transition stageMap
    rw [← MonoidAlgebra.mapDomainRingHom_comp, ← MonoidAlgebra.mapDomainRingHom_comp]
    congr 1
    apply MonoidHom.ext
    intro q
    exact QuotientGroup.induction_on q (fun _ ↦ rfl)
  calc
    _ = stageMap Λ e he N' (CompletedGroupRing.transition Λ G hc (x.val _)) :=
      DFunLike.congr_fun hsquare _
    _ = _ := congrArg (stageMap Λ e he N') (x.property hc)

/-- The completed-ring map is specified at every open-normal quotient. -/
def hom : completedGroupRing Λ G →+* completedGroupRing Λ H where
  toFun x :=
    ⟨fun N ↦ stageMap Λ e he N (x.val (N.comap e.toMonoidHom he)), compatible Λ e he x⟩
  map_zero' := by
    apply completedGroupRing.ext
    intro N
    exact (stageMap Λ e he N).map_zero
  map_one' := by
    apply completedGroupRing.ext
    intro N
    exact (stageMap Λ e he N).map_one
  map_add' := by
    intro x y
    apply completedGroupRing.ext
    intro N
    exact (stageMap Λ e he N).map_add _ _
  map_mul' := by
    intro x y
    apply completedGroupRing.ext
    intro N
    exact (stageMap Λ e he N).map_mul _ _

variable (heinv : Continuous e.symm)

/-- Applying the inverse continuous group equivalence recovers the compatible family. -/
theorem hom_symm_hom (x : completedGroupRing Λ G) :
    hom Λ e.symm heinv (hom Λ e he x) = x := by
  apply completedGroupRing.ext
  intro N
  have h : (N.comap e.symm.toMonoidHom heinv).comap e.toMonoidHom he ≤ N := by
    intro g hg
    change e.symm (e g) ∈ N at hg
    simpa using hg
  have hcomp :
      (stageMap Λ e.symm heinv N).comp
          (stageMap Λ e he (N.comap e.symm.toMonoidHom heinv)) =
        CompletedGroupRing.transition Λ G h := by
    unfold stageMap CompletedGroupRing.transition
    rw [← MonoidAlgebra.mapDomainRingHom_comp]
    congr 1
    apply MonoidHom.ext
    intro q
    refine QuotientGroup.induction_on q (fun g ↦ ?_)
    change (QuotientGroup.mk (e.symm (e g)) : G ⧸ N.toSubgroup) = QuotientGroup.mk g
    rw [e.symm_apply_apply]
  change stageMap Λ e.symm heinv N
    (stageMap Λ e he (N.comap e.symm.toMonoidHom heinv) (x.val _)) = x.val N
  calc
    _ = CompletedGroupRing.transition Λ G h (x.val _) := DFunLike.congr_fun hcomp _
    _ = _ := x.property h

/-- The inverse also uses the actual inverse continuous equivalence on all
finite-stage projections. Mixed group/coefficient universes are retained. -/
def ringEquiv : completedGroupRing Λ G ≃+* completedGroupRing Λ H where
  toFun := hom Λ e he
  invFun := hom Λ e.symm heinv
  left_inv := hom_symm_hom Λ e he heinv
  right_inv := hom_symm_hom Λ e.symm heinv he
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
