/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.Regular.Frobenius
import StacksCheckRecall

@[expose] public section

universe u

/- Lemma 51.17.6 (Kunz): a Noetherian ring in which the prime `p` vanishes is
regular if and only if its `p`-power Frobenius endomorphism is flat. -/
@[stacks 0EC0]
#check (isRegularRing_iff_frobenius_flat :
  ∀ (p : ℕ) [Fact p.Prime] (A : Type u) [CommRing A] [IsNoetherianRing A]
    (hp : (p : A) = 0), IsRegularRing A ↔ (RingHom.frobeniusOfPrime p hp).Flat)
