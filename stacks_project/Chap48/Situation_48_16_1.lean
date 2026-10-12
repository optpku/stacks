/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.FiniteTypeSeparatedOver
import StacksCheckRecall

@[expose] public section

universe u

open AlgebraicGeometry

section

variable (S : Scheme.{u}) [IsNoetherian S]

/- Situation 48.16.1: for a Noetherian scheme `S`, `Scheme.FiniteTypeSeparatedOver S` is the
full category of schemes over `S` whose structure morphisms are separated and of finite type;
its morphisms are morphisms of schemes over `S`. -/
@[stacks 0F42] #check
  (AlgebraicGeometry.Scheme.FiniteTypeSeparatedOver S : Type (u + 1))

end
