/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.Henselian.StrictHenselian.EtaleRetraction
import StacksCheckRecall

@[expose] public section

universe u

/- Lemma 61.8.5: if every faithfully flat étale ring map out of `A` has a
retraction, then the local ring of `A` at a maximal ideal is strictly henselian. -/
@[stacks 097V] #check
  (Algebra.HasFaithfullyFlatEtaleRetraction.strictlyHenselian_atMaximalIdeal :
    ∀ {A : Type u} [CommRing A] [Algebra.HasFaithfullyFlatEtaleRetraction A]
      (m : Ideal A) [m.IsMaximal], StrictHenselianLocalRing (Localization.AtPrime m))
