/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.WeaklyAssociatedPoints.GenericPoints

@[expose] public section

universe u

/- Lemma 31.5.12: The weakly associated points of a reduced scheme are exactly the generic points
of its irreducible components. -/
@[stacks 0EME] #check
  (AlgebraicGeometry.Scheme.weakAss_eq_genericPoints :
    ∀ (X : AlgebraicGeometry.Scheme.{u}) [AlgebraicGeometry.IsReduced X],
      X.weakAss = genericPoints X)

#check
  (AlgebraicGeometry.Scheme.mem_weakAss_iff_mem_genericPoints :
    ∀ (X : AlgebraicGeometry.Scheme.{u}) [AlgebraicGeometry.IsReduced X] (x : X),
      x ∈ X.weakAss ↔ x ∈ genericPoints X)
