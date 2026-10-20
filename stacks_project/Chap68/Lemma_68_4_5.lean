/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Etale.FiniteAbove
import StacksCheckRecall

open CategoryTheory AlgebraicGeometry

universe u

/- Lemma 68.4.5: For a point of an algebraic space, the six finite-fibre and
quasi-compact field-valued representative conditions are equivalent. -/
@[stacks 03JV] #check (AlgebraicGeometry.AlgebraicSpace.finiteAbove_tfae :
  ∀ {S : Scheme.{u}} (X : AlgebraicSpace S)
    (x : AlgebraicGeometry.AlgebraicSpace.Points X),
    List.TFAE
      [ AlgebraicGeometry.AlgebraicSpace.forallAffineEtaleFiniteAbove X x
      , AlgebraicGeometry.AlgebraicSpace.existsEtaleCoverFiniteAbove X x
      , AlgebraicGeometry.AlgebraicSpace.existsMonoFieldValuedFiniteAffineFibres X x
      , AlgebraicGeometry.AlgebraicSpace.existsQuasiCompactMonoFieldValuedPoint X x
      , AlgebraicGeometry.AlgebraicSpace.existsQuasiCompactFieldValuedPoint X x
      , AlgebraicGeometry.AlgebraicSpace.forallFieldValuedPointQuasiCompact X x ])
