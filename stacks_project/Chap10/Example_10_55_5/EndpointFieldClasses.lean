/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.GrothendieckGroup.Basic
public import ReasLib.RingTheory.Polynomial.Equalizer.Finite
import StacksCheckRecall

/-!
# Endpoint-field ingredients for Example 10.55.5

@stack 00JG

The endpoint action and its finiteness are owned by `Polynomial.EqualEndpoint`.  The former
item-local K-theory staging declarations had no downstream consumers.
-/

@[expose] public section

open CategoryTheory

@[stacks 00JG "common-endpoint evaluation"]
#check @Polynomial.EqualEndpoint.eval

@[stacks 00JG "finite endpoint module"]
#check @Polynomial.EqualEndpoint.endpointModuleFinite

@[stacks 00JG "finite-module K-class"]
#check @ModuleCat.K0.finiteOf
