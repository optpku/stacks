/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Sites.Topos.Factorization.Special
public import StacksCheckRecall.CommandCrossRef

/-!
# Remark 7.29.8

Common replacement sites for equivalences of topoi are reusable factorization
API owned by `MorphismOfTopoiIn.Factorization.CommonSite`.
-/

@[expose] public section

/- Remark 7.29.8 (03CK): an equivalence of topoi has a common subcanonical
finite-limit site with special-cocontinuous presentations from both sides. -/
@[stacks 03CK "common site"] #check @CategoryTheory.MorphismOfTopoiIn.Factorization.CommonSite

@[stacks 03CK "existence"] #check @CategoryTheory.MorphismOfTopoiIn.Factorization.CommonSite.exists_of_equivalence

@[stacks 03CK "comparison"] #check @CategoryTheory.MorphismOfTopoiIn.Factorization.CommonSite.cocontinuousComparisonIso
