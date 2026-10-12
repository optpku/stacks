/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Correspondence.Monoidal

@[expose] public section

open CategoryTheory

universe u

/- Compatibility bridge for the symmetric monoidal structure on rational Chow
correspondences. -/
#check (AlgebraicGeometry.Correspondence.instSymmetricCategory :
  ∀ {k : Type u} [Field k],
    SymmetricCategory (AlgebraicGeometry.Correspondence.Category k))
