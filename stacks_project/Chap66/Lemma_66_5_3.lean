/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.QuasiCompact.Coproduct
import StacksCheckRecall

/-!
# Finite coproducts of quasi-compact algebraic spaces

A finite disjoint union of quasi-compact algebraic spaces is again quasi-compact.
-/

universe u v

/- Lemma 66.5.3: a finite disjoint union of quasi-compact algebraic spaces is a
quasi-compact algebraic space. -/
@[stacks 040T] #check (AlgebraicGeometry.AlgebraicSpace.instIsQuasiCompact_coproduct :
  ∀ {S : AlgebraicGeometry.Scheme.{u}} {I : Type v} [Finite I]
    (X : I → AlgebraicGeometry.AlgebraicSpace S)
    [∀ i, AlgebraicGeometry.AlgebraicSpace.IsQuasiCompact (X i)],
    AlgebraicGeometry.AlgebraicSpace.IsQuasiCompact
      (AlgebraicGeometry.AlgebraicSpace.coproduct X))
