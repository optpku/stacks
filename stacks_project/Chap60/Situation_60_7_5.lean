/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
import ReasLib.AlgebraicGeometry.Crystalline.Base

open CategoryTheory AlgebraicGeometry

universe u

variable (p : ℕ) [Fact (Nat.Prime p)]

/- Situation 60.7.5: The source's `S₀ = V(I)` is the canonical `ideal.subscheme`,
with inclusion `ideal.subschemeι`; the complete setup is bundled by `Base p`. -/
@[stacks 07MF] #check (AlgebraicGeometry.Scheme.Crystalline.Base p : Type (u + 1))
