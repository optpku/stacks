/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Correspondence.GradedCategory

@[expose] public section

open CategoryTheory

universe u

/- Compatibility bridge for the symmetric monoidal structure on graded Chow
correspondences. -/
#check (AlgebraicGeometry.Correspondence.GradedCategory.instSymmetricCategory :
  ∀ {k : Type u} [Field k],
    SymmetricCategory (AlgebraicGeometry.Correspondence.GradedCategory k))
