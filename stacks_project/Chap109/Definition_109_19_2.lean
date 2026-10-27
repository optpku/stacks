/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Curve.RelativeDualizingSheaf
import StacksCheckRecall

@[expose] public section

universe u

open CategoryTheory

/- Definition 109.19.2: for a family of curves `f : X ⟶ S` with Cohen–Macaulay
fibres equidimensional of dimension 1, the relative dualizing sheaf is the
`𝒪_X`-module `sheaf C = cohomologySheaf C.complex (-1)` studied in
Lemma 109.19.1. -/
@[stacks 0E6Q] #check (AlgebraicGeometry.AlgebraicSpace.RelativeDualizingComplex.sheaf :
  ∀ {S : AlgebraicGeometry.Scheme.{u}} {X Y : AlgebraicGeometry.AlgebraicSpace S}
    {f : X ⟶ Y},
    [AlgebraicGeometry.AlgebraicSpace.Spaces.Curves.IsFamily f] →
    [AlgebraicGeometry.AlgebraicSpace.CohenMacaulay f] →
    [AlgebraicGeometry.AlgebraicSpace.RelativeDimension f 1] →
    (C : AlgebraicGeometry.AlgebraicSpace.RelativeDualizingComplex f) → X.Modules)
