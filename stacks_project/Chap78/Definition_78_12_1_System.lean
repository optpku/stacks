/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Groupoid.Quasicoherent

/-!
# Quasi-coherent modules on groupoids in algebraic spaces

A quasi-coherent module on a groupoid in algebraic spaces is a pair `(F, α)`
with `F` quasi-coherent on the object space and `α : t^* F ⟶ s^* F` satisfying
the cocycle law on `R ×_{s, U, t} R` and `e^* α = 𝟙`.
-/

open CategoryTheory AlgebraicGeometry
open GroupoidAlgebraicSpace

universe u

variable {S : Scheme.{u}} {B : AlgebraicSpace S} (G : GroupoidAlgebraicSpace B)

#check (AlgebraicGeometry.GroupoidAlgebraicSpace.System G : Type (u + 1))
#check (AlgebraicGeometry.GroupoidAlgebraicSpace.System.of :
  (F : AlgebraicSpace.QCoh G.U.left) →
  (action : (AlgebraicSpace.QCoh.pullback G.t.left).obj F ⟶
    (AlgebraicSpace.QCoh.pullback G.s.left).obj F) →
  Cocycle G F action → Unit G F action → System G)
