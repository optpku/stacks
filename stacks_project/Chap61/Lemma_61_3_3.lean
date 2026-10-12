/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.LocalIso
public import ReasLib.RingTheory.RingHom.Local.Properties
import StacksCheckRecall

/- Lemma 61.3.3: local isomorphisms compose, and maps identifying local rings
compose. This tagged check is part (2), whose canonical owner is
`RingHom.IsIsoOnLocalRings.stableUnderComposition`. -/
@[stacks 096G] #check
  (RingHom.IsIsoOnLocalRings.stableUnderComposition :
    RingHom.StableUnderComposition RingHom.IsIsoOnLocalRings)

/- Part (1): local isomorphisms compose. -/
#check
  (Algebra.IsLocalIso.trans :
    ∀ (R S : Type*) [CommSemiring R] [CommSemiring S] [Algebra R S]
      (T : Type*) [CommSemiring T] [Algebra S T] [Algebra R T]
      [IsScalarTower R S T] [Algebra.IsLocalIso R S] [Algebra.IsLocalIso S T],
      Algebra.IsLocalIso R T)
