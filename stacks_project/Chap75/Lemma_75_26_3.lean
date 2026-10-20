/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.FiberEulerCharacteristic

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

/- Lemma 75.26.3: if `S` is a scheme, `X` is an algebraic space over `S`, and `E` in
`D(𝒪_X)` is perfect, then the Euler characteristic of the derived residue-field fiber of
`E` is locally constant on `Points X`. -/
@[stacks 0D1Z] #check
  (AlgebraicGeometry.AlgebraicSpace.ModuleDerived.fiberEulerChar_isLocallyConstant :
    ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} (E : ModuleDerived X),
      ModuleDerived.IsPerfect E →
        IsLocallyConstant (ModuleDerived.fiberEulerChar E))
