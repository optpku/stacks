/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Points.QuasiCompact
import StacksCheckRecall

@[expose] public section

universe u

/- Lemma 66.5.2: let `S` be a scheme. Let `X` be an algebraic space over `S`. Then `X` is
quasi-compact if and only if `|X|` is quasi-compact. -/
@[stacks 03E4] #check (AlgebraicGeometry.AlgebraicSpace.isQuasiCompact_iff_compactSpace :
  ∀ {S : AlgebraicGeometry.Scheme.{u}} (X : AlgebraicGeometry.AlgebraicSpace S),
    AlgebraicGeometry.AlgebraicSpace.IsQuasiCompact X ↔
      CompactSpace (AlgebraicGeometry.AlgebraicSpace.Points X))
