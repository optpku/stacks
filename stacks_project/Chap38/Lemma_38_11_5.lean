/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Flat.DenseOpen
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open scoped AlgebraicGeometry

universe u

/- Lemma 38.11.5: a separated, locally finite-type, flat morphism that is an
isomorphism over a retrocompact scheme-theoretically dense open is an open immersion. -/
@[stacks 081M] #check
  (AlgebraicGeometry.IsOpenImmersion.of_isIso_restrict_of_flat :
    ∀ {X S : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ S),
      [AlgebraicGeometry.IsSeparated f] →
      [AlgebraicGeometry.LocallyOfFiniteType f] →
      [AlgebraicGeometry.Flat f] →
      (U : S.Opens) →
      [IsIso (f ∣_ U)] →
      IsRetrocompact (U : Set S) →
      AlgebraicGeometry.schemeTheoreticallyDense U →
      AlgebraicGeometry.IsOpenImmersion f)
