/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.GroupScheme.QuasiProjective

@[expose] public section

universe u

open AlgebraicGeometry CategoryTheory

#check
  (AlgebraicGeometry.GroupScheme.instQuasiProjective :
    ∀ {k : Type u} [Field k] (G : SchemeOverField k) [GrpObj G] [Algebraic G],
      QuasiProjective G.hom)
