module

public import ReasLib.AlgebraicGeometry.Scheme.Normal.Nagata.Japanese
import StacksCheckRecall

@[expose] public section

/-!
# Remark 28.13.2

One possible condition on a locally Noetherian scheme requires every quotient
of every stalk by an associated prime to be Japanese. This is not adopted as a
global definition: the cited examples give a one-dimensional Noetherian domain
whose excellent, hence Japanese, local rings do not force its normalization to
be finite.

The alternative condition requires every quotient of every affine section ring
by an associated prime to be Japanese. For integral schemes, this affine
condition implies the established affine-local predicate `Scheme.IsJapanese`.
-/

open AlgebraicGeometry
open scoped AlgebraicGeometry

universe u

#check (AlgebraicGeometry.Scheme.isJapaneseAtStalkAssociatedPrimes_iff :
  ∀ X : Scheme.{u},
    AlgebraicGeometry.Scheme.IsJapaneseAtStalkAssociatedPrimes X ↔
      IsLocallyNoetherian X ∧
        ∀ (x : X) (p : PrimeSpectrum (X.presheaf.stalk x)),
          IsAssociatedPrime p.asIdeal (X.presheaf.stalk x) →
            IsN2Ring (X.presheaf.stalk x ⧸ p.asIdeal))

/- Remark 28.13.2: the affine associated-prime formulation of the Japanese
condition. -/
@[stacks 033T] #check
  (AlgebraicGeometry.Scheme.isJapaneseAtAffineAssociatedPrimes_iff :
    ∀ X : Scheme.{u},
      AlgebraicGeometry.Scheme.IsJapaneseAtAffineAssociatedPrimes X ↔
        ∀ (U : X.affineOpens) (p : PrimeSpectrum (Γ(X, U))),
          IsAssociatedPrime p.asIdeal (Γ(X, U)) →
            IsN2Ring (Γ(X, U) ⧸ p.asIdeal))
