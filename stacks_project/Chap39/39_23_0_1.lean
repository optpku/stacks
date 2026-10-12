/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import ReasLib.Algebra.Ring.Subring.EqLocus
import StacksCheckRecall

universe u v

variable (A : Type u) (B : Type v) [CommRing A] [CommRing B]
variable (sSharp tSharp : A →+* B)

/- 39.23.0.1: The invariant ring `C` is the subring `tSharp.eqLocus sSharp` of
elements `a : A` satisfying `tSharp a = sSharp a`. -/
@[stacks 03BF] #check
  (RingHom.coe_eqLocus tSharp sSharp :
    (tSharp.eqLocus sSharp : Set A) = {a | tSharp a = sSharp a})
