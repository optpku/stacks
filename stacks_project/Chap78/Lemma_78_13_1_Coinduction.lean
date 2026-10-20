/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Groupoid.Quasicoherent.Coinduction

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.GroupoidAlgebraicSpace.QCoh

#check
  (AlgebraicGeometry.GroupoidAlgebraicSpace.QCoh.forgetCoinductionAdjunction :
    ∀ {S : Scheme.{u}} {B : AlgebraicSpace S} (G : GroupoidAlgebraicSpace B)
      [AlgebraicSpace.Flat G.s.left] [AlgebraicSpace.Flat G.t.left]
      [AlgebraicSpace.QuasiCompact G.s.left] [AlgebraicSpace.QuasiCompact G.t.left]
      [AlgebraicSpace.QuasiSeparated G.s.left] [AlgebraicSpace.QuasiSeparated G.t.left],
      forget G ⊣ coinduction G)

end AlgebraicGeometry.GroupoidAlgebraicSpace.QCoh
