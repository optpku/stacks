/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.DeligneMumford
import StacksCheckRecall

@[expose] public section

universe u

/- Lemma 94.13.1 (1): let `S` be a scheme contained in `Sch_fppf`. A category
fibred in groupoids `X` over `(Sch/S)_fppf` which is representable by an
algebraic space is a Deligne-Mumford stack. -/
@[stacks 03YS]
#check (AlgebraicGeometry.DeligneMumfordStack.of_isRepresentableByAlgebraicSpace :
  ∀ {S : AlgebraicGeometry.Scheme.{u}} {X : AlgebraicGeometry.GroupoidsOver S},
    AlgebraicGeometry.IsRepresentableByAlgebraicSpace X →
      AlgebraicGeometry.DeligneMumfordStack X)

/- Lemma 94.13.1 (2): if `F` is an algebraic space over `S`, then the associated
category fibred in groupoids `F.toGroupoids` is a Deligne-Mumford stack. -/
@[stacks 03YS]
#check (AlgebraicGeometry.DeligneMumfordStack.ofAlgebraicSpace :
  ∀ {S : AlgebraicGeometry.Scheme.{u}} (F : AlgebraicGeometry.AlgebraicSpace S),
    AlgebraicGeometry.DeligneMumfordStack F.toGroupoids)

/- Lemma 94.13.1 (3): if `X` is an object of `(Sch/S)_fppf`, then
`GroupoidsOver.slice X` is a Deligne-Mumford stack. -/
@[stacks 03YS]
#check (AlgebraicGeometry.DeligneMumfordStack.slice :
  ∀ {S : AlgebraicGeometry.Scheme.{u}} (U : CategoryTheory.Over S),
    AlgebraicGeometry.DeligneMumfordStack (AlgebraicGeometry.GroupoidsOver.slice U))
