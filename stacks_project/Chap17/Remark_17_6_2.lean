/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Topology.Sheaf.Support.ClosedSubset.Functor
import StacksCheckRecall

/-!
# Remark 17.6.2

The closed-support construction is owned by
`TopCat.Sheaf.ClosedSubset.SectionsWithSupport`.  This chapter entry deliberately recalls that
direct API instead of adding source-local aliases.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite TopCat TopologicalSpace

universe u

/- Remark 17.6.2 (01AY) (1): on each open set, the closed-support subobject consists exactly of
sections whose support lies in the closed subset. -/
@[stacks 01AY "(1)"]
#check fun {X : TopCat.{u}} {Z : Set X} (hZ : IsClosed Z)
    (F : X.Sheaf AddCommGrpCat.{u}) (U : Opens X) ↦
  TopCat.Sheaf.ClosedSubset.SectionsWithSupport.subsheaf_app_range hZ F U

/- Remark 17.6.2 (01AY) (2): it is the largest abelian subsheaf supported on `Z`. -/
@[stacks 01AY "(2)"]
#check fun {X : TopCat.{u}} {Z : Set X} (hZ : IsClosed Z)
    (F : X.Sheaf AddCommGrpCat.{u}) ↦
  (TopCat.Sheaf.ClosedSubset.SectionsWithSupport.isGreatest_subsheaf hZ F :
    IsGreatest
      { G : Subobject F | abelianSheafSupport G ⊆ Z }
      (TopCat.Sheaf.ClosedSubset.SectionsWithSupport.subsheaf hZ F))

/- Remark 17.6.2 (01AY) (3): restriction to `Z` makes closed support functorial. -/
@[stacks 01AY "(3)"]
#check fun {X : TopCat.{u}} {Z : Set X} (hZ : IsClosed Z) ↦
  (TopCat.Sheaf.ClosedSubset.SectionsWithSupport.functor hZ :
    X.Sheaf AddCommGrpCat.{u} ⥤ (TopCat.of Z).Sheaf AddCommGrpCat.{u})

/- Remark 17.6.2 (01AY) (4): the closed-support functor is left exact. -/
@[stacks 01AY "(4)"]
#check fun {X : TopCat.{u}} {Z : Set X} (hZ : IsClosed Z) ↦
  (TopCat.Sheaf.ClosedSubset.SectionsWithSupport.functorLeftExact hZ :
    leftExactFunctor (X.Sheaf AddCommGrpCat.{u})
      ((TopCat.of Z).Sheaf AddCommGrpCat.{u})
      (TopCat.Sheaf.ClosedSubset.SectionsWithSupport.functor hZ))

/- The kernel presentation uses restriction to the open complement. -/
#check TopCat.Sheaf.ClosedSubset.SectionsWithSupport.restrictionToComplement
