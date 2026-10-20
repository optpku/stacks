/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import ReasLib.AlgebraicGeometry.Scheme.Sites.Fppf.Comparison
import StacksCheckRecall

universe u

/- Lemma 34.7.2: Any syntomic covering is an fppf covering, and consequently so is any
smooth, étale, or Zariski covering. -/
@[stacks 021N] #check
  (AlgebraicGeometry.Scheme.bigSyntomicPrecoverage_le_fppfPrecoverage.{u} :
    AlgebraicGeometry.Scheme.bigSyntomicPrecoverage.{u} ≤
      AlgebraicGeometry.Scheme.fppfPrecoverage.{u})

#check
  (AlgebraicGeometry.Scheme.bigSmoothPrecoverage_le_fppfPrecoverage.{u} :
    AlgebraicGeometry.Scheme.bigSmoothPrecoverage.{u} ≤
      AlgebraicGeometry.Scheme.fppfPrecoverage.{u})

#check
  (AlgebraicGeometry.Scheme.etalePrecoverage_le_fppfPrecoverage.{u} :
    AlgebraicGeometry.Scheme.etalePrecoverage.{u} ≤
      AlgebraicGeometry.Scheme.fppfPrecoverage.{u})

#check
  (AlgebraicGeometry.Scheme.zariskiPrecoverage_le_fppfPrecoverage.{u} :
    AlgebraicGeometry.Scheme.zariskiPrecoverage.{u} ≤
      AlgebraicGeometry.Scheme.fppfPrecoverage.{u})
