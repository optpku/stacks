/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import ReasLib.AlgebraicGeometry.AlgebraicSpace.FiniteTypePoints.Monomorphism
import StacksCheckRecall

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/- Lemma 67.25.7 -/
@[stacks 06EL] #check
  (AlgebraicGeometry.AlgebraicSpace.isFiniteTypePoint_tfae :
    ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} (x : Points X),
      List.TFAE [IsFiniteTypePoint x, existsSingletonLocallyOfFiniteType x,
        existsEtaleFieldMono x])

end AlgebraicGeometry.AlgebraicSpace
