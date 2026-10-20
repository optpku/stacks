/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import ReasLib.AlgebraicGeometry.AlgebraicSpace.OpenSubspace.QuasiCompact
import StacksCheckRecall

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

/- Lemma 70.14.1: for an open subspace of a quasi-compact quasi-separated
algebraic space, quasi-compactness of the inclusion, quasi-compactness of the
open subspace, and a finite type quasi-coherent ideal defining the closed
complement are equivalent. -/
@[stacks 0855] #check
  (AlgebraicGeometry.AlgebraicSpace.OpenSubspace.quasiCompact_tfae :
    ∀ {S : Scheme.{u}} {X : AlgebraicSpace S}
      [IsQuasiCompact X] [IsAbsolutelyQuasiSeparated X] (U : OpenSubspace X),
      List.TFAE [QuasiCompact U.ι, IsQuasiCompact U.X,
        OpenSubspace.existsFiniteTypeVanishingIdeal U])
