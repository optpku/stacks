/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Groupoid.Quasicoherent.Action
import StacksCheckRecall

universe u

open AlgebraicGeometry CategoryTheory
open GroupoidAlgebraicSpace

/- Lemma 78.12.2: Let `B → S` as in Section 78.3. Let `(U, R, s, t, c)` be a
groupoid in algebraic spaces over `B`. If `(F, α)` is a quasi-coherent module on
`(U, R, s, t, c)` then `α` is an isomorphism. -/
@[stacks 077W] #check (AlgebraicGeometry.GroupoidAlgebraicSpace.QCoh.action_isIso :
  ∀ {S : Scheme.{u}} {B : AlgebraicSpace S} {G : GroupoidAlgebraicSpace B} (A : G.QCoh),
    IsIso A.action)

/- Companion: the bundled isomorphism with inverse obtained by reindexing along inversion. -/
#check (AlgebraicGeometry.GroupoidAlgebraicSpace.QCoh.actionIso :
  ∀ {S : Scheme.{u}} {B : AlgebraicSpace S} {G : GroupoidAlgebraicSpace B} (A : G.QCoh),
    (AlgebraicSpace.QCoh.pullback G.t.left).obj A.obj ≅
      (AlgebraicSpace.QCoh.pullback G.s.left).obj A.obj)

/- Companion: the inverse morphism obtained by reindexing the equivariance map along inversion. -/
#check (AlgebraicGeometry.GroupoidAlgebraicSpace.QCoh.actionInverse :
  ∀ {S : Scheme.{u}} {B : AlgebraicSpace S} {G : GroupoidAlgebraicSpace B} (A : G.QCoh),
    (AlgebraicSpace.QCoh.pullback G.s.left).obj A.obj ⟶
      (AlgebraicSpace.QCoh.pullback G.t.left).obj A.obj)

