/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap64.Proposition_64_29_3_CompletedGroupRingAlgebra

@[expose] public section
open CategoryTheory
open scoped MonoidAlgebra
noncomputable section
universe r v w m

namespace ActualCompletedRingTransport
variable (Λ : Type r) [CommRing Λ]
variable {G : Type v} {H : Type w}
variable [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
variable (e : G ≃* H) (he : Continuous e)

/-- Pull back an open normal subgroup using the given continuous map.
No topology is transported along an arbitrary abstract group equivalence. -/
def comap (N : OpenNormalSubgroup H) : OpenNormalSubgroup G :=
  ⟨N.toOpenSubgroup.comap e.toMonoidHom he,
    show (N.toSubgroup.comap e.toMonoidHom).Normal from N.isNormal'.comap e.toMonoidHom⟩

/-- The actual induced map on the corresponding group quotients. -/
def quotientMap (N : OpenNormalSubgroup H) :
    G ⧸ (comap e he N).toSubgroup →* H ⧸ N.toSubgroup :=
  QuotientGroup.map (comap e he N).toSubgroup N.toSubgroup e.toMonoidHom (by intro x hx; exact hx)

/-- Map the actual finite-stage group-algebra coefficients along the quotient map. -/
def stageMap (N : OpenNormalSubgroup H) :
    MonoidAlgebra Λ (G ⧸ (comap e he N).toSubgroup) →+* MonoidAlgebra Λ (H ⧸ N.toSubgroup) :=
  MonoidAlgebra.mapDomainRingHom Λ (quotientMap e he N)

theorem compatible (x : completedGroupRing Λ G) :
    CompletedGroupRing.IsCompatible Λ H (fun N ↦ stageMap Λ e he N (x.val (comap e he N))) := sorry

/-- The completed-ring map is specified at every open-normal quotient. -/
def hom : completedGroupRing Λ G →+* completedGroupRing Λ H where
  toFun x := ⟨fun N ↦ stageMap Λ e he N (x.val (comap e he N)), compatible Λ e he x⟩
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
    (ringEquiv Λ e he heinv x).val N = stageMap Λ e he N (x.val (comap e he N)) := rfl

/-- Scalar transport preserves the underlying module and its maps. -/
def restrictScalars : ModuleCat.{m} (completedGroupRing Λ G) ⥤ ModuleCat.{m} (completedGroupRing Λ H) :=
  ModuleCat.restrictScalars (ringEquiv Λ e he heinv).symm.toRingHom

end ActualCompletedRingTransport
