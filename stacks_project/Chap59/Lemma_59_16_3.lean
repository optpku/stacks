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

variable (A B : Type u) [CommRing A] [CommRing B] [Algebra A B]
  [Module.FaithfullyFlat A B]

/- Lemma 59.16.3: for a faithfully flat algebra A → B, the coefficient-A
extended Amitsur complex is acyclic, expressing exactness in positive degrees
and H^0 = A. -/
@[stacks 03O9] #check
  (Algebra.Amitsur.extended.acyclicOfFaithfullyFlat (R := A) (A := B) (M := A) :
    (Algebra.Amitsur.extended A B A).Acyclic)
