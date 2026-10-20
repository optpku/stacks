/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.CochainDGAlgebra.Free.Resolution
import StacksCheckRecall

@[expose] public section

universe u v

variable {R : Type u} [CommRing R]
variable (B : CochainDGAlgebra.{u, v} R)

/-!
# Lemma 22.38.1 (0BZ7)

The source replacement is owned by
`CochainDGAlgebra.Free.KFlatResolution`: it packages the resolving DGA, its
free graded-algebra presentation, K-flatness, and the quasi-isomorphism to the
target. No partial generator-adjoining constructor is exposed.
-/

@[stacks 0BZ7] #check
  (CochainDGAlgebra.Free.KFlatResolution.nonempty B :
    Nonempty (CochainDGAlgebra.Free.KFlatResolution.{u, v, v} B))
