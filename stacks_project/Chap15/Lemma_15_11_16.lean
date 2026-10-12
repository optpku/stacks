/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.Henselian.ZeroLocus.Connected
import StacksCheckRecall

/-!
# Lemma 15.11.16

@stack 09Y6
-/

@[expose] public section

universe u

namespace PrimeSpectrum

variable {A : Type u} [CommRing A]
variable (I : Ideal A) [HenselianRing A I] (p : PrimeSpectrum A)

-- Lemma 15.11.16 (09Y6): for a henselian pair `(A, I)` and a prime `p`, the closed
-- subset `V(p + I)` of `PrimeSpectrum A` is connected.
@[stacks 09Y6]
#check
  (connectedSpace_zeroLocus_prime_add_of_henselianRing I p :
    ConnectedSpace (zeroLocus (((p.asIdeal + I : Ideal A) : Set A))))

end PrimeSpectrum
