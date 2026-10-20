/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Proetale.AffineIndEtale

universe u

#check
  (AlgebraicGeometry.Scheme.ProEt.affineIndEtaleTopology :
    ∀ (S : AlgebraicGeometry.Scheme.{u}) [AlgebraicGeometry.IsAffine S],
      CategoryTheory.GrothendieckTopology
        (AlgebraicGeometry.Scheme.ProEt.AffineIndEtale S))
