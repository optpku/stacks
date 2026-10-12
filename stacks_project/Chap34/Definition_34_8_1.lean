/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Cover.Ph
import StacksCheckRecall

@[expose] public section

universe u

namespace AlgebraicGeometry

variable (T : Scheme.{u}) [IsAffine T]

/- Definition 34.8.1: a standard ph covering of an affine scheme `T` is a proper
surjective morphism to `T` together with a finite affine-open cover of its source. -/
@[stacks 0DBD] #check (AlgebraicGeometry.StandardPhCovering T : Type (u + 1))

end AlgebraicGeometry
