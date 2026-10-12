/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap111.Exercise_111_49_3_Associated
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry.Scheme

/- Exercise 111.49.3: On any scheme, assign to an effective Cartier divisor the
Cartier divisor obtained by gluing its local nonzerodivisor equations as a global
section of 𝒦_S^⁎ / 𝒪_S^⁎. -/
@[stacks 02F6] #check @cartierDivisor_ofEffectiveCartier
