/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import ReasLib.AlgebraicGeometry.PuncturedSpectrum
import ReasLib.AlgebraicGeometry.Scheme.Module.Picard.UniqueFactorization
import ReasLib.RingTheory.UniqueFactorizationDomain.RegularLocal
import StacksCheckRecall

universe u

variable (A : Type u) [CommRing A] [IsRegularLocalRing A]

/- Lemma 52.27.5: the Picard group of the punctured spectrum of a regular local ring
is trivial. -/
@[stacks 0F2H] #check
  (AlgebraicGeometry.Scheme.subsingleton_picardGroup_openSubscheme_Spec_of_uniqueFactorizationMonoid
      A (AlgebraicGeometry.PuncturedSpectrum.puncturedOpen A) :
    Subsingleton
      (AlgebraicGeometry.Scheme.PicardGroup
        (AlgebraicGeometry.PuncturedSpectrum.scheme A)))
