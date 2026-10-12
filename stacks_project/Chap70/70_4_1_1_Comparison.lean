/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Sheaf

/-!
# Presheaf functors of algebraic spaces
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

#check (AlgebraicGeometry.AlgebraicSpace.forgetToPresheaf :
  ∀ {S : Scheme.{u}}, AlgebraicSpace S ⥤ ((Over S)ᵒᵖ ⥤ Type u))
