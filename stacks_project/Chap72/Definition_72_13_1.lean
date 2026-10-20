/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Geometrically
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry CommRingCat
open AlgebraicGeometry.AlgebraicSpace

universe u

section

variable {k : Type u} [Field k] (X : AlgebraicSpace (Spec (of k))) [IsDecent X]

/- 0DMU::statement_repair::1 — Definition 72.13.1: A decent algebraic space X over a field k is geometrically
irreducible if |X_{k'}| is irreducible after every field extension k'/k.
Irreducible spaces are nonempty by convention. -/
@[stacks 0DMU] #check
  (AlgebraicGeometry.AlgebraicSpace.GeometricallyIrreducible.iff X :
    GeometricallyIrreducible X ↔
      ∀ (K : Type u) [Field K] [Algebra k K],
        IrreducibleSpace (Points (baseChange (Spec.map (ofHom (algebraMap k K))) X)))

end
