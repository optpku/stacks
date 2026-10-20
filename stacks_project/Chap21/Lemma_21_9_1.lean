/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Sites.Cech.DeltaFunctor
import StacksCheckRecall

@[expose] public section

/- Lemma 21.9.1 (Tag 03AQ): for a fixed-target family whose iterated fibre products exist,
the associated additive-presheaf Cech cochain functor is exact. -/

@[stacks 03AQ "fixed-target Cech cochain functor"]
#check @CategoryTheory.Cech.FixedTarget.cochainFunctor

@[stacks 03AQ "exact fixed-target Cech cochain functor"]
#check @CategoryTheory.Cech.FixedTarget.cochainFunctor_exact
