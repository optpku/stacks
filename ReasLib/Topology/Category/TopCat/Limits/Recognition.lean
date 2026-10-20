/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Topology.Category.TopCat.Limits.Basic
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Recognition of Limits in `TopCat`

This leaf turns a limiting cone of underlying types plus a preimage-basis
description into a limiting cone in `TopCat`. It does not require the index
category to be cofiltered.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Set TopologicalSpace

universe u v w

namespace TopCat

namespace Cone

variable {J : Type v} [Category.{w} J]
variable {F : J ⥤ TopCat.{max v u}} (c : Cone F)

/-- The preimage-basis condition identifies the topology on a cone point with
the infimum of the topologies induced by its projections. -/
theorem topology_eq_iInf_induced_of_forgetIsLimit_of_preimageBasis
    (h_limit : IsLimit ((forget TopCat).mapCone c))
    (h_basis :
      IsTopologicalBasis
        {U : Set c.pt | ∃ (j : J) (V : Set (F.obj j)), IsOpen V ∧ U = c.π.app j ⁻¹' V}) :
    c.pt.str = ⨅ j, (F.obj j).str.induced (c.π.app j) := sorry

/-- The identity from the canonical induced-topology cone point to `c.pt` is
continuous when the two cone-point topologies agree. -/
theorem continuous_canonicalPoint_to_point
    (h_top : c.pt.str = ⨅ j, (F.obj j).str.induced (c.π.app j)) :
    @Continuous
      (TopCat.conePtOfConeForget ((forget TopCat).mapCone c)) c.pt
      (TopCat.topologicalSpaceConePtOfConeForget ((forget TopCat).mapCone c)) c.pt.str
      id := sorry

/-- The identity from `c.pt` to the canonical induced-topology cone point is
continuous when the two cone-point topologies agree. -/
theorem continuous_point_to_canonicalPoint
    (h_top : c.pt.str = ⨅ j, (F.obj j).str.induced (c.π.app j)) :
    @Continuous
      c.pt (TopCat.conePtOfConeForget ((forget TopCat).mapCone c)) c.pt.str
      (TopCat.topologicalSpaceConePtOfConeForget ((forget TopCat).mapCone c))
      id := sorry

/-- The explicit identity homeomorphism from the canonical induced-topology
cone point to `c.pt`. -/
def pointHomeomorphOfTopologyEq
    (h_top : c.pt.str = ⨅ j, (F.obj j).str.induced (c.π.app j)) :
    (TopCat.coneOfConeForget ((forget TopCat).mapCone c)).pt ≃ₜ c.pt :=
  { toEquiv := Equiv.refl c.pt
    continuous_toFun := continuous_canonicalPoint_to_point c h_top
    continuous_invFun := continuous_point_to_canonicalPoint c h_top }

/-- The identity homeomorphism intertwines the projections of the canonical
induced-topology cone and `c`. -/
@[reassoc]
theorem pointHomeomorphOfTopologyEq_fac
    (h_top : c.pt.str = ⨅ j, (F.obj j).str.induced (c.π.app j)) (j : J) :
    (TopCat.coneOfConeForget ((forget TopCat).mapCone c)).π.app j =
      (TopCat.isoOfHomeo (pointHomeomorphOfTopologyEq c h_top)).hom ≫ c.π.app j := sorry

/-- The canonical induced-topology cone is isomorphic to `c` when their point
topologies agree. -/
def isoOfTopologyEq
    (h_top : c.pt.str = ⨅ j, (F.obj j).str.induced (c.π.app j)) :
    TopCat.coneOfConeForget ((forget TopCat).mapCone c) ≅ c :=
  Cone.ext (TopCat.isoOfHomeo (pointHomeomorphOfTopologyEq c h_top))
    (pointHomeomorphOfTopologyEq_fac c h_top)

/-- The vertex map of the hom of `isoOfTopologyEq` is induced by the identity
homeomorphism of the two cone points. -/
@[simp]
theorem isoOfTopologyEq_hom_hom
    (h_top : c.pt.str = ⨅ j, (F.obj j).str.induced (c.π.app j)) :
    (isoOfTopologyEq c h_top).hom.hom =
      (TopCat.isoOfHomeo (pointHomeomorphOfTopologyEq c h_top)).hom := sorry

/-- A `TopCat` cone is limiting when its underlying cone of types is limiting
and its projection preimages form a topological basis. -/
@[stacks 0A2Q]
def isLimit_of_forgetIsLimit_of_preimageBasis
    (h_limit : IsLimit ((forget TopCat).mapCone c))
    (h_basis :
      IsTopologicalBasis
        {U : Set c.pt | ∃ (j : J) (V : Set (F.obj j)), IsOpen V ∧ U = c.π.app j ⁻¹' V}) :
    IsLimit c :=
  IsLimit.ofIsoLimit
    (TopCat.isLimitConeOfForget ((forget TopCat).mapCone c) h_limit)
    (isoOfTopologyEq c
      (topology_eq_iInf_induced_of_forgetIsLimit_of_preimageBasis c h_limit h_basis))

end Cone

end TopCat
