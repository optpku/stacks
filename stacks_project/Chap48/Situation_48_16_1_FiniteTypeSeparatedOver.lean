/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.FiniteTypeSeparatedOver

@[expose] public section

universe u

open AlgebraicGeometry

section

variable (S : Scheme.{u}) [IsNoetherian S]

/- The shared category has the expected universe over a Noetherian base scheme. -/
#check (AlgebraicGeometry.Scheme.FiniteTypeSeparatedOver S : Type (u + 1))

end
