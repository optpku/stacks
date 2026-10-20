/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Stratification.Finite

open AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

#check
  (AlgebraicGeometry.AlgebraicSpace.exists_finiteSchemeStratumFiltration :
    ∀ {S : Scheme.{u}} (X : AlgebraicSpace S) [IsQuasiCompact X] [IsReasonable X],
      Nonempty (FiniteSchemeStratumFiltration X))

end AlgebraicGeometry.AlgebraicSpace
