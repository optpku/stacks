/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.Ring.Colimits
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Universe-polymorphic colimits of commutative rings

Mathlib constructs all colimits in `CommRingCat`. This leaf exposes the universe-lifted
`HasColimitsOfSize` instance in the same style as `AddCommGrpCat.hasColimitsOfSize`, so consumers
do not need to rebuild it inside geometric namespaces.
-/

@[expose] public section

open CategoryTheory

universe a b w

namespace CommRingCat

/-- Commutative rings in universe `w` admit colimits indexed by any object and morphism
universes that lift into `w`. -/
@[stacks 03D6 "universe-polymorphic commutative-ring colimits"]
instance (priority := 100) hasColimitsOfSize
    [UnivLE.{a, w}] [UnivLE.{b, w}] :
    Limits.HasColimitsOfSize.{a, b} CommRingCat.{w} :=
  Limits.hasColimitsOfSizeOfUnivLE.{w, w, a, b} CommRingCat.{w}

end CommRingCat
