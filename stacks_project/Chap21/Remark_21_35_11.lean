/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Monoidal.Closed.PullbackComparison
import StacksCheckRecall

@[expose] public section

/-!
# Remark 21.35.11

Pullback of an internal Hom is governed by the objectwise tensor comparison of the pullback
functor.  This construction is independent of ringed sites and derived categories, and is owned
by the generic `Functor.PullbackInternalHom` API.
-/

/- Remark 21.35.11 (08JF): the pulled-back evaluation map. -/
@[stacks 08JF "pullback internal-Hom evaluation"] #check
  @CategoryTheory.Functor.PullbackInternalHom.evaluation

/- Remark 21.35.11 (08JF): the canonical pullback/internal-Hom comparison. -/
@[stacks 08JF "pullback internal-Hom comparison"] #check
  @CategoryTheory.Functor.PullbackInternalHom.comparison

@[stacks 08JF "pullback internal-Hom braided specification"] #check
  @CategoryTheory.Functor.PullbackInternalHom.comparison_spec

@[stacks 08JF "pullback internal-Hom uncurried specification"] #check
  @CategoryTheory.Functor.PullbackInternalHom.comparison_uncurry
