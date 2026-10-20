/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Point.SchematicLocus

/-!
# The schematic locus of an algebraic space

Every algebraic space has a largest open subspace which is a scheme.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/- Lemma 66.13.1: Let `S` be a scheme. Let `X` be an algebraic space over `S`.
There exists a largest open subspace of `X` which is a scheme. -/
@[stacks 03JH] #check (AlgebraicGeometry.AlgebraicSpace.exists_largest_open_scheme :
    ∀ {S : Scheme.{u}} (X : AlgebraicSpace S),
    ∃ U : OpenSubspace X, IsScheme U.X ∧
      ∀ (V : OpenSubspace X), IsScheme V.X →
        ∃ f : V.X ⟶ U.X, f ≫ U.ι = V.ι)

end AlgebraicGeometry.AlgebraicSpace
