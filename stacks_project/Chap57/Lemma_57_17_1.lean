/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.FiniteTypeOver.Countable
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open AlgebraicGeometry

universe u

/- Lemma 57.17.1: Let `R` be a countable Noetherian ring. Then the category of schemes of
finite type over `R` is countable. -/
@[stacks 0G0U] #check
  (AlgebraicGeometry.Scheme.countableCategory_finiteTypeOver :
    ∀ (R : Type u) [CommRing R] [Countable R] [IsNoetherianRing R],
      CountableCategory (Skeleton (Scheme.FiniteTypeOver (Spec (CommRingCat.of R)))))
