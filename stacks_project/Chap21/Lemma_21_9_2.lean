/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Sites.Cech.DeltaFunctor
import StacksCheckRecall

@[expose] public section

/- Lemma 21.9.2 (Tag 03AR): the fixed-target Cech cohomology functors and their connecting
morphisms form a cohomological delta functor. -/

@[stacks 03AR "fixed-target Cech cohomology functor"]
#check @CategoryTheory.Cech.FixedTarget.cohomologyFunctor

@[stacks 03AR "fixed-target Cech delta functor"]
#check @CategoryTheory.Cech.FixedTarget.deltaFunctor

@[stacks 03AR "fixed-target Cech connecting morphism"]
#check @CategoryTheory.Cech.FixedTarget.connecting
