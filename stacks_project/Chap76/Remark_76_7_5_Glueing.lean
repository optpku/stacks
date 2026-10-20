/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Differentials.Descent

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.QCoh

universe u

/- The canonical relative differential sheaf as a quasi-coherent module. -/
#check (AlgebraicGeometry.AlgebraicSpace.Hom.Differentials.packedRelativeDifferentials :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (h : X ⟶ Y), QCoh X)
