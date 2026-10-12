/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.LinearAlgebra.ExteriorAlgebra.Determinant.Invertible
import StacksCheckRecall

/-!
# Remark 15.119.1

@stack 0FJA

The determinant line of a finite projective module is the submodule of its exterior algebra
annihilated by all degree-one generators.  ReasLib exposes it with the notation `det[R](M)`.
-/

@[stacks 0FJA "determinant action"]
#check @Module.Determinant.action

@[stacks 0FJA "Remark 15.119.1 determinant submodule"]
#check @Module.Determinant.submodule

@[stacks 0FJA "membership in the determinant submodule"]
#check @Module.Determinant.mem_iff

@[stacks 0FJA "determinant inclusion"]
#check @Module.Determinant.ι

@[stacks 0FJA "finite-projective determinant line is invertible"]
#check @Module.Determinant.instInvertible
