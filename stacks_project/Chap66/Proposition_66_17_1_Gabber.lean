/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Fpqc
import StacksCheckRecall

/-!
# Algebraic spaces as fpqc sheaves

An algebraic space over a scheme `S` is defined as an fppf sheaf on schemes over `S`.
Gabber's theorem upgrades this to sheafness for the induced fpqc topology on `Over S`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

/- Proposition 66.17.1 (Gabber): let `S` be a scheme and let `X` be an algebraic space
over `S`. Then `X.functorOfPoints` is a sheaf for `Scheme.fpqcTopology.over S` on the
big site of schemes over `S`. -/
@[stacks 0APL] #check (AlgebraicGeometry.AlgebraicSpace.isSheaf_fpqc :
  ∀ {S : Scheme.{u}} (X : AlgebraicSpace S),
    Presheaf.IsSheaf (Scheme.fpqcTopology.over S) X.functorOfPoints)
