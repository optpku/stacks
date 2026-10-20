/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import ReasLib.AlgebraicGeometry.AlgebraicSpace.Groupoid.Quasicoherent.Pullback
import ReasLib.AlgebraicGeometry.AlgebraicSpace.Groupoid.Quasicoherent.Pushforward
import ReasLib.AlgebraicGeometry.AlgebraicSpace.Groupoid.Quasicoherent.Adjunction
import StacksCheckRecall

universe u

open AlgebraicGeometry CategoryTheory Limits

variable {S : Scheme.{u}} {B : AlgebraicSpace S}
variable {G H : GroupoidAlgebraicSpace B} (f : GroupoidAlgebraicSpace.Hom G H)
variable [AlgebraicSpace.QuasiCompact f.obj.left] [AlgebraicSpace.QuasiSeparated f.obj.left]
variable [AlgebraicSpace.Flat H.s.left] [AlgebraicSpace.Flat H.t.left]
variable (h_target : IsPullback f.arrow.left G.t.left H.t.left f.obj.left)

/- Lemma 78.12.4 (1): if `f : GroupoidAlgebraicSpace.Hom G H` is quasi-compact and
quasi-separated on objects, the target square along `t, t'` is cartesian, and `s', t'` are
flat, then `(F, α) ↦ (f_* F, f_* α)` is a functor `G.QCoh ⥤ H.QCoh`. -/
@[stacks 0GPM] #check
  (AlgebraicGeometry.GroupoidAlgebraicSpace.QCoh.pushforward f h_target : G.QCoh ⥤ H.QCoh)

/- Lemma 78.12.4 (2): the pushforward of (1) is right adjoint to the pullback of
Lemma 78.12.3. -/
@[stacks 0GPM] #check
  (AlgebraicGeometry.GroupoidAlgebraicSpace.QCoh.pullbackPushforwardAdjunction f h_target :
    AlgebraicGeometry.GroupoidAlgebraicSpace.QCoh.pullback f ⊣
      AlgebraicGeometry.GroupoidAlgebraicSpace.QCoh.pushforward f h_target)

/- Companion checks: the functor is built from `pushforwardObj` / `pushforwardMap`, and the
adjunction cells restrict to the module adjunction along `f.obj.left`. -/
#check GroupoidAlgebraicSpace.QCoh.pushforwardObj
#check GroupoidAlgebraicSpace.QCoh.pushforwardMap
#check GroupoidAlgebraicSpace.QCoh.adjunctionUnit_hom
#check GroupoidAlgebraicSpace.QCoh.adjunctionCounit_hom
