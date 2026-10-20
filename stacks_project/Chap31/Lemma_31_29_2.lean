/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.RankOneReflexive.ClassGroup
import StacksCheckRecall

/-!
# Lemma 31.29.2

Rank-one reflexive coherent modules and the Weil divisor class group.

@stack 0EBM
-/

@[expose] public section

universe u

/- Lemma 31.29.2: For an integral locally Noetherian normal scheme, the group of isomorphism
classes of rank-one coherent reflexive modules is isomorphic to the Weil divisor class group. -/
@[stacks 0EBM] #check
  (AlgebraicGeometry.Scheme.Modules.rankOneReflexiveClassGroup_addEquiv_weilDivisorClassGroup :
    ∀ {X : AlgebraicGeometry.Scheme.{u}} [AlgebraicGeometry.IsIntegral X]
      [AlgebraicGeometry.IsLocallyNoetherian X] (hXnormal : X.isNormal),
      Nonempty
        (AlgebraicGeometry.Scheme.Modules.rankOneReflexiveClassGroup hXnormal ≃+
          AlgebraicGeometry.WeilDivisorClassGroup X))
