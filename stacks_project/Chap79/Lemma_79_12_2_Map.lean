/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FinitePart.OpenImmersion

/-! # Covariance of the finite-part sheaf along open immersions -/

open CategoryTheory AlgebraicGeometry AlgebraicSpace Opposite

universe u

#check (AlgebraicGeometry.AlgebraicSpace.finitePartOpenMap :
  ∀ {S : Scheme.{u}} {X' X Y : AlgebraicSpace S} {f' : X' ⟶ Y} {f : X ⟶ Y}
    (j : X' ⟶ X) [IsOpenImmersion j] (hcomm : j ≫ f = f'),
    finitePartSheaf f' ⟶ finitePartSheaf f)
