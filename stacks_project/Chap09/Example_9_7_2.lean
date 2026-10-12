/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import StacksCheckRecall

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

/- Example 9.7.2: the canonical `ℝ`-basis of `ℂ` is the ordered pair `(1, I)`, so `ℂ` is a
two-dimensional `ℝ`-vector space and hence a finite extension of `ℝ` of degree `2`. -/
#check Complex.coe_basisOneI

/- Example 9.7.2: the complex numbers form a degree-`2` extension of the real numbers; this is
exactly the canonical finite-rank theorem. -/
@[stacks 09G4]
#check (Complex.finrank_real_complex : Module.finrank ℝ ℂ = 2)
