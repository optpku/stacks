/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Separation.ZariskiLocal
import StacksCheckRecall

@[expose] public section

universe u

/- Lemma 66.6.6: Relative and absolute Zariski-local quasi-separatedness are equivalent to the
existence of a Zariski covering with quasi-compact surjective étale affine atlases, optionally
mapping into affine opens of the base. -/
@[stacks 03W7] #check
  (AlgebraicGeometry.AlgebraicSpace.isZariskiLocallyQuasiSeparated_tfae :
    ∀ {S : AlgebraicGeometry.Scheme.{u}} (X : AlgebraicGeometry.AlgebraicSpace S),
      List.TFAE [AlgebraicGeometry.AlgebraicSpace.IsZariskiLocallyQuasiSeparated X,
        AlgebraicGeometry.AlgebraicSpace.IsAbsolutelyZariskiLocallyQuasiSeparated X,
        AlgebraicGeometry.AlgebraicSpace.HasQuasiCompactAffineEtaleZariskiCover X,
        AlgebraicGeometry.AlgebraicSpace.HasQuasiCompactAffineEtaleZariskiCoverOnAffineBase X])
