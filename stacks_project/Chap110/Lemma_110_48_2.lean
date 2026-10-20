/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.GroupScheme.Counterexamples
import StacksCheckRecall

@[expose] public section

universe u

open AlgebraicGeometry
open scoped AlgebraicGeometry

/- Lemma 110.48.2: there exists a group scheme over infinite-dimensional affine
space which is flat and of finite type, but not quasi-separated. -/
@[stacks 08IX] #check
  (AlgebraicGeometry.GroupScheme.exists_flat_finiteType_not_quasiSeparated_over_infiniteAffineSpace :
    ∀ {k : Type u} [Field k],
      ∃ G : AlgebraicGeometry.GroupScheme (𝔸(ULift.{u} ℕ; Spec (CommRingCat.of k))),
        AlgebraicGeometry.Flat G.X.hom ∧ Scheme.Hom.FiniteType G.X.hom ∧
          ¬ AlgebraicGeometry.QuasiSeparated G.X.hom)
