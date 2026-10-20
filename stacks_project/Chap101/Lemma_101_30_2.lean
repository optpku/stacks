/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Points.Spectral
import StacksCheckRecall

/-!
# Spectral spaces of quasi-compact quasi-separated algebraic stacks

A quasi-compact quasi-separated algebraic stack has spectral space of points.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicStack

/- Lemma 101.30.2: Let `X` be a quasi-compact and quasi-separated algebraic stack.
Then `|X|` is a spectral topological space. -/
@[stacks 0DQP] #check (AlgebraicGeometry.AlgebraicStack.instSpectralSpacePoints :
  ∀ {S : Scheme.{u}} (X : GroupoidsOver S)
    [AlgebraicStack X] [IsQuasiCompact X] [IsQuasiSeparated X], SpectralSpace (Points X))

end AlgebraicGeometry.AlgebraicStack
