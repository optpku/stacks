/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Topology.Sheaf.Subset.Closed
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopCat TopologicalSpace

universe u

/- Lemma 17.6.1 (01AX) (1): pushforward along the inclusion of a closed subset is exact on
abelian sheaves. -/
@[stacks 01AX "(1)"]
#check fun {X : TopCat.{u}} {Z : Set X} (hZ : IsClosed Z) ↦
  (TopCat.Sheaf.ClosedSubset.AddCommGrp.pushforwardExact hZ :
    exactFunctor ((TopCat.of Z).Sheaf AddCommGrpCat.{u})
      (X.Sheaf AddCommGrpCat.{u})
      (Sheaf.pushforward AddCommGrpCat.{u} (TopCat.subsetInclusion Z)))

/- Lemma 17.6.1 (01AX) (2): pushforward along a closed-subset inclusion is fully faithful. -/
@[stacks 01AX "(2)"]
#check fun {X : TopCat.{u}} {Z : Set X} (_ : IsClosed Z) ↦
  (TopCat.Sheaf.Subset.fullyFaithful Z :
    (Sheaf.pushforward AddCommGrpCat.{u}
      (TopCat.subsetInclusion Z)).FullyFaithful)

/- Lemma 17.6.1 (01AX) (3): the essential image consists exactly of abelian sheaves whose
support is contained in the closed subset. -/
@[stacks 01AX "(3)"]
#check fun {X : TopCat.{u}} {Z : Set X} (hZ : IsClosed Z)
    (F : X.Sheaf AddCommGrpCat.{u}) ↦
  (TopCat.Sheaf.ClosedSubset.AddCommGrp.essImage_iff_support_subset hZ F :
    (Sheaf.pushforward AddCommGrpCat.{u}
      (TopCat.subsetInclusion Z)).essImage F ↔
      abelianSheafSupport F ⊆ Z)

/- Lemma 17.6.1 (01AX) (4): pullback is a left inverse to pushforward along the closed-subset
inclusion, expressed by invertibility of the adjunction counit. -/
@[stacks 01AX "(4)"]
#check fun {X : TopCat.{u}} {Z : Set X} (_ : IsClosed Z) ↦
  (TopCat.Sheaf.Subset.counit_isIso Z :
    IsIso (Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u}
      (TopCat.subsetInclusion Z)).counit)
