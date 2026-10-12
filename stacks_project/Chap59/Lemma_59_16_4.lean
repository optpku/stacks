/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Amitsur.Acyclic
import StacksCheckRecall

@[expose] public section

universe u

/- Lemma 59.16.4: if `A → B` is faithfully flat, then the Amitsur complex
with coefficients in an `A`-module `M` is exact in positive degrees and has
degree-zero cohomology `M`. -/
@[stacks 03OA] #check
  (@Algebra.Amitsur.extended.acyclicOfFaithfullyFlat :
    ∀ (A B M : Type u) [CommRing A] [CommRing B] [Algebra A B]
      [Module.FaithfullyFlat A B] [AddCommGroup M] [Module A M],
      (Algebra.Amitsur.extended A B M).Acyclic)
