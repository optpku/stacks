/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.GoldenInteger
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry.GoldenIntegerQuasiSection

/- Exercise 111.34.7 (1): `instIsClosedImmersion` asserts
`IsClosedImmersion closedImmersion` for the inclusion of `scheme` into
`ambient = Spec (Localization.Away (X * (X - 1) * (2 * X - 1)))`. -/
@[stacks 0299] #check
  (AlgebraicGeometry.GoldenIntegerQuasiSection.instIsClosedImmersion :
    AlgebraicGeometry.IsClosedImmersion
      AlgebraicGeometry.GoldenIntegerQuasiSection.closedImmersion)

/- Exercise 111.34.7 (2): the structure morphism `toSpecInt` is finite. -/
@[stacks 0299] #check
  (AlgebraicGeometry.GoldenIntegerQuasiSection.instIsFinite_toSpecInt :
    AlgebraicGeometry.IsFinite AlgebraicGeometry.GoldenIntegerQuasiSection.toSpecInt)

/- Exercise 111.34.7 (3): the structure morphism `toSpecInt` is surjective. -/
@[stacks 0299] #check
  (AlgebraicGeometry.GoldenIntegerQuasiSection.instSurjective_toSpecInt :
    AlgebraicGeometry.Surjective AlgebraicGeometry.GoldenIntegerQuasiSection.toSpecInt)
