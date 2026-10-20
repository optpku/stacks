/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import ReasLib.CategoryTheory.Functor.Derived.ComputesAt
import StacksCheckRecall

@[expose] public section

/-!
# Definition 13.14.10

The source computation conditions are the neutral pointwise-derived API:
pointwise definedness together with invertibility of the identity denominator comparison.
-/

@[stacks 05SX] #check @CategoryTheory.Functor.RightDerived.ComputesAt

@[stacks 05SX] #check @CategoryTheory.Functor.RightDerived.ComputesAt.objects

@[stacks 05SX] #check @CategoryTheory.Functor.LeftDerived.ComputesAt

@[stacks 05SX] #check @CategoryTheory.Functor.LeftDerived.ComputesAt.objects

@[stacks 05SX] #check @CategoryTheory.Functor.RightDerived.ComputesAt.iff

@[stacks 05SX] #check @CategoryTheory.Functor.LeftDerived.ComputesAt.iff
