/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
import ReasLib.AlgebraicGeometry.Scheme.Divisor.EffectiveCartier.Complement.Existence

open CategoryTheory Limits TopologicalSpace

universe u

/- Lemma 31.16.7: a dense affine open in a Noetherian scheme with affine diagonal is the
complement of an effective Cartier divisor when all local rings off the open are unique
factorization domains. -/
@[stacks 0EGJ] #check
  (AlgebraicGeometry.Scheme.OpenComplement.exists_effectiveCartierDivisor_of_affineDiagonal :
    ∀ {X : AlgebraicGeometry.Scheme.{u}} [AlgebraicGeometry.IsNoetherian X]
      [AlgebraicGeometry.IsAffineHom (prod.lift (𝟙 X) (𝟙 X))] {U : X.Opens},
      AlgebraicGeometry.IsAffineOpen U → Dense (U : Set X) →
        (∀ x : X, x ∉ (U : Set X) →
          UniqueFactorizationMonoid (X.presheaf.stalk x)) →
        ∃ D : X.IdealSheafData,
          AlgebraicGeometry.IsEffectiveCartierDivisor D.subschemeι ∧ U = D.openComplement)
