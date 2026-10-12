/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import Mathlib.AlgebraicGeometry.Morphisms.Immersion

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

variable {Z X S : Scheme.{u}} (i : Z ⟶ X) (f : X ⟶ S)
variable [IsImmersion i] [IsSeparated f]

/- Lemma 26.23.9: a locally closed subscheme of a scheme separated over
`S` is separated over `S`. -/
@[stacks 01L8] #check (inferInstance : IsSeparated (i ≫ f))
