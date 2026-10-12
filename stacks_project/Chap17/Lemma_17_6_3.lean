/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Topology.Sheaf.Support.ClosedSubset.Adjunction
import StacksCheckRecall

/-!
# Lemma 17.6.3

The closed-subset pushforward/sections-with-support adjunction is directly provided by
`TopCat.Sheaf.ClosedSubset.SectionsWithSupport`.  The chapter no longer maintains a parallel
namespace or scoped notation for that API.
-/

#check TopCat.Sheaf.ClosedSubset.SectionsWithSupport.object
#check TopCat.Sheaf.ClosedSubset.SectionsWithSupport.sheaf
#check TopCat.Sheaf.ClosedSubset.SectionsWithSupport.subsheafMap_w
#check TopCat.Sheaf.ClosedSubset.SectionsWithSupport.subsheafMap
#check TopCat.Sheaf.ClosedSubset.SectionsWithSupport.functor
#check TopCat.Sheaf.ClosedSubset.SectionsWithSupport.subsheafPushforwardEqTop
#check TopCat.Sheaf.ClosedSubset.SectionsWithSupport.objectUnitIsIso
#check TopCat.Sheaf.ClosedSubset.SectionsWithSupport.counitAppIsIso
#check TopCat.Sheaf.ClosedSubset.SectionsWithSupport.inclusionPushforwardInv
#check TopCat.Sheaf.ClosedSubset.SectionsWithSupport.inclusionPushforward_hom_inv_id
#check TopCat.Sheaf.ClosedSubset.SectionsWithSupport.inclusionPushforward_inv_hom_id
#check TopCat.Sheaf.ClosedSubset.SectionsWithSupport.inclusionPushforwardIso
#check TopCat.Sheaf.ClosedSubset.SectionsWithSupport.pullbackPushforwardCounitAppInv
#check TopCat.Sheaf.ClosedSubset.SectionsWithSupport.pullbackPushforwardCounitApp_hom_inv_id
#check TopCat.Sheaf.ClosedSubset.SectionsWithSupport.pullbackPushforwardCounitApp_inv_hom_id
#check TopCat.Sheaf.ClosedSubset.SectionsWithSupport.pullbackPushforwardCounitAppIso
#check TopCat.Sheaf.ClosedSubset.SectionsWithSupport.objectPullbackPushforwardUnitAppInv
#check TopCat.Sheaf.ClosedSubset.SectionsWithSupport.objectPullbackPushforwardUnitApp_hom_inv_id
#check TopCat.Sheaf.ClosedSubset.SectionsWithSupport.objectPullbackPushforwardUnitApp_inv_hom_id
#check TopCat.Sheaf.ClosedSubset.SectionsWithSupport.objectPullbackPushforwardUnitAppIso
#check TopCat.Sheaf.ClosedSubset.SectionsWithSupport.unitApp
#check TopCat.Sheaf.ClosedSubset.SectionsWithSupport.counitApp
@[expose] public section

open CategoryTheory CategoryTheory.Limits TopCat TopologicalSpace

universe u

/- Lemma 17.6.3 (01AZ) (1): pushforward from a closed subset is left adjoint to the sheaf of
sections supported on that subset. -/
@[stacks 01AZ "(1)"]
#check fun {X : TopCat.{u}} {Z : Set X} (hZ : IsClosed Z) ↦
  (TopCat.Sheaf.ClosedSubset.SectionsWithSupport.adjunction hZ :
    Sheaf.pushforward AddCommGrpCat.{u} (TopCat.subsetInclusion Z) ⊣
      TopCat.Sheaf.ClosedSubset.SectionsWithSupport.functor hZ)

/- Lemma 17.6.3 (01AZ) (2): pushforward from a closed subset preserves arbitrary colimits. -/
@[stacks 01AZ "(2)"]
#check fun {X : TopCat.{u}} {Z : Set X} (hZ : IsClosed Z) ↦
  (TopCat.Sheaf.ClosedSubset.SectionsWithSupport.pushforwardPreservesColimitsOfIsClosed
      (X := X) (Z := Z) hZ :
    PreservesColimits
      (Sheaf.pushforward AddCommGrpCat.{u} (TopCat.subsetInclusion Z)))
