/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.GroupScheme.QuasiProjective

@[expose] public section

universe u

open AlgebraicGeometry CategoryTheory

/- Lemma 39.8.7: the structure morphism of an algebraic group scheme over a field is
quasi-projective. -/
@[stacks 0BF7] #check
  (AlgebraicGeometry.GroupScheme.instQuasiProjective :
    ∀ {k : Type u} [Field k] (G : SchemeOverField k) [GrpObj G] [Algebraic G],
      QuasiProjective G.hom)
