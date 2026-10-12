/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.ArithmeticFibers
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped AlgebraicGeometry

/- Exercise 111.51.5: a finite-type morphism to `Spec ℤ` with nonempty fibers over infinitely
many primes has nonempty generic fiber, while the analogous statement for locally finite-type
morphisms fails. -/
@[stacks 02FK] #check
  (AlgebraicGeometry.nonempty_pullback_specRat_of_infinite_nonempty_pullback_specZMod :
    ∀ {X : Scheme} (f : X ⟶ Spec (CommRingCat.of ℤ)) [Scheme.Hom.FiniteType f],
      {p : ℕ | p.Prime ∧
          Nonempty (pullback f (AlgebraicGeometry.specZModToSpecInt p) : Scheme)}.Infinite →
        Nonempty (pullback f AlgebraicGeometry.specRatToSpecInt : Scheme))

/- The explicit locally finite-type counterexample to the analogous implication. -/
@[stacks 02FK] #check
  (AlgebraicGeometry.exists_locallyOfFiniteType_counterexample :
    ∃ (X : Scheme) (f : X ⟶ Spec (CommRingCat.of ℤ)),
      LocallyOfFiniteType f ∧
        {p : ℕ | p.Prime ∧
            Nonempty (pullback f (AlgebraicGeometry.specZModToSpecInt p) : Scheme)}.Infinite ∧
          IsEmpty (pullback f AlgebraicGeometry.specRatToSpecInt : Scheme))

end
