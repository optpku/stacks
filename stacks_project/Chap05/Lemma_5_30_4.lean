/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Topology.Category.ProfiniteGrp.Recognition
import StacksCheckRecall

@[expose] public section

/- Lemma 5.30.4: the shared `ProfiniteGrp` recognition API separates the two useful limit
presentation predicates from the source's three-way equivalence. -/
@[stacks 0BR1 "finite discrete and cofiltered finite discrete presentations"]
#check ProfiniteGrp.profinite_tfae

@[stacks 0BR1 "finite discrete limit presentation"]
#check ProfiniteGrp.HasFiniteLimitPresentation

@[stacks 0BR1 "cofiltered finite discrete limit presentation"]
#check ProfiniteGrp.HasCofilteredFiniteLimitPresentation

/- Presentation witnesses retain their indexing category, finite-group diagram, and chosen
continuous group isomorphism for downstream use. -/
#check ProfiniteGrp.FiniteLimitPresentation
#check ProfiniteGrp.FiniteLimitPresentation.ofContinuousMulEquiv
#check ProfiniteGrp.CofilteredFiniteLimitPresentation
#check ProfiniteGrp.CofilteredFiniteLimitPresentation.ofContinuousMulEquiv
#check ProfiniteGrp.CofilteredFiniteLimitPresentation.ofProfiniteGrp
#check ProfiniteGrp.CofilteredFiniteLimitPresentation.ofCompactTotallyDisconnected
#check OpenNormalSubgroup.top
#check OpenNormalSubgroup.mem_top
#check OpenNormalSubgroup.coe_top
#check OpenNormalSubgroup.toSubgroup_top
#check fun {G : Type} [Group G] [TopologicalSpace G]
  (P : ProfiniteGrp.CofilteredFiniteLimitPresentation G) ↦ P.diagram
#check fun {G : Type} [Group G] [TopologicalSpace G]
  (P : ProfiniteGrp.CofilteredFiniteLimitPresentation G) ↦
  (inferInstance : CategoryTheory.SmallCategory P.index)
#check fun {G : Type} [Group G] [TopologicalSpace G]
  (P : ProfiniteGrp.CofilteredFiniteLimitPresentation G) ↦
  (inferInstance : CategoryTheory.IsCofiltered P.index)
